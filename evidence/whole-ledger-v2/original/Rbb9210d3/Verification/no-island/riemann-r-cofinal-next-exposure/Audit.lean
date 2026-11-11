import Lean
import Lean.Replay
set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
open Lean
structure Stage where
 label : String
 modules : Array String
 base : Array String
 deriving FromJson
structure Config where
 entry : String
 stages : Array Stage
 output : String
 progress : String
 current : String
 deriving FromJson
private def require (ok : Bool) (why : String) : IO Unit :=
 unless ok do throw (IO.userError why)
private def kind : ConstantInfo → String
 | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
 | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
 | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
private def sameStoredInfo (a b : ConstantInfo) : Bool :=
 kind a == kind b && a.name == b.name && a.levelParams == b.levelParams &&
 a.type == b.type && a.value? (allowOpaque := true) == b.value? (allowOpaque := true)
private def sameFullInfo (a b : ConstantInfo) : Bool :=
 match a,b with
 | .defnInfo x,.defnInfo y => x == y
 | .thmInfo x,.thmInfo y => x == y
 | .opaqueInfo x,.opaqueInfo y => x == y
 | .ctorInfo x,.ctorInfo y => x == y
 | .recInfo x,.recInfo y => x == y
 | .axiomInfo x,.axiomInfo y => sameStoredInfo a b && x.isUnsafe == y.isUnsafe
 | .inductInfo x,.inductInfo y =>
   sameStoredInfo a b && x.numParams == y.numParams && x.numIndices == y.numIndices &&
   x.all == y.all && x.ctors == y.ctors && x.numNested == y.numNested &&
   x.isRec == y.isRec && x.isUnsafe == y.isUnsafe && x.isReflexive == y.isReflexive
 | .quotInfo x,.quotInfo y =>
   sameStoredInfo a b && (match x.kind,y.kind with
    | .type,.type | .ctor,.ctor | .lift,.lift | .ind,.ind => true
    | _,_ => false)
 | _,_ => false
private def axioms (env : Kernel.Environment) (roots : Array Name) : IO (Array Name × Nat) := do
 let mut todo := roots
 let mut seen : NameSet := {}
 let mut result : NameSet := {}
 while !todo.isEmpty do
  let n := todo.back!
  todo := todo.pop
  if seen.contains n then continue
  seen := seen.insert n
  let some ci := env.find? n | throw (IO.userError s!"MISSING_AXIOM_DEPENDENCY {n}")
  match ci with
  | .axiomInfo _ => result := result.insert n
  | _ =>
    for child in ci.getUsedConstantsAsSet do
     unless seen.contains child do todo := todo.push child
 return (result.toList.toArray,seen.size)
private def binderNames (e : Expr) : Array String := Id.run do
 let mut e := e
 let mut out := #[]
 while let .forallE n _ body _ := e do
  out := out.push n.toString
  e := body
 return out
namespace QueryCompatReplay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  owners : Std.HashMap Name Name
  currentFile : System.FilePath
  logFile : System.FilePath

structure State where
  env : Kernel.Environment
  checkedCalls : Nat := 0
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

/-- Add a declaration, possibly throwing a `Kernel.Exception`. -/
def addDecl (d : Declaration) : M Unit := do
  let name := d.getTopLevelNames.head!
  let ctx ← read
  let owner := (ctx.owners[name]?).map Name.toString
  let started ← IO.monoMsNow
  let before := Json.mkObj [("phase",toJson "kernel-start"),("CI",toJson name.toString),
    ("owner",toJson owner),("monotonic_ms",toJson started),("completed_kernel_calls",toJson (← get).checkedCalls)]
  IO.FS.writeFile ctx.currentFile (before.pretty ++ "\n")
  IO.FS.withFile ctx.logFile IO.FS.Mode.append fun file => file.putStrLn before.compress
  match (← get).env.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env =>
    modify fun s => {s with env := env, checkedCalls := s.checkedCalls + 1}
    let after := Json.mkObj [("phase",toJson "kernel-done"),("CI",toJson name.toString),
      ("owner",toJson owner),("elapsed_ms",toJson ((← IO.monoMsNow)-started)),
      ("completed_kernel_calls",toJson (← get).checkedCalls)]
    IO.FS.writeFile ctx.currentFile (after.pretty ++ "\n")
    IO.FS.withFile ctx.logFile IO.FS.Mode.append fun file => file.putStrLn after.compress
  | .error ex =>
    let failed := Json.mkObj [("phase",toJson "kernel-error"),("CI",toJson name.toString),
      ("owner",toJson owner),("elapsed_ms",toJson ((← IO.monoMsNow)-started))]
    IO.FS.writeFile ctx.currentFile (failed.pretty ++ "\n")
    IO.FS.withFile ctx.logFile IO.FS.Mode.append fun file => file.putStrLn failed.compress
    throwKernelException ex

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo   info =>
          addDecl (Declaration.defnDecl   info)
        | .thmInfo    info =>
          -- Ignore duplicate theorems. This code is identical to that in `finalizeImport` before it
          -- added extended duplicates support for the module system, which is not relevant for us
          -- here as we always load all .olean information. We need this case *because* of the module
          -- system -- as we have more data loaded than it, we might encounter duplicate private
          -- theorems where elaboration under the module system would have only one of them in scope.
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              return
          addDecl (Declaration.thmDecl    info)
        | .axiomInfo  info =>
          addDecl (Declaration.axiomDecl  info)
        | .opaqueInfo info =>
          addDecl (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          -- Make sure we are really finished with the constructors.
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (Declaration.inductDecl lparams nparams types false)
        -- We postpone checking constructors,
        -- and at the end make sure they are identical
        -- to the constructors generated when we replay the inductives.
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        -- Similarly we postpone checking recursors.
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          -- `Quot.lift` and `Quot.ind` have types that reference `Eq`,
          -- so we need to ensure `Eq` is replayed before adding the quotient declaration.
          replayConstant `Eq
          addDecl (Declaration.quotDecl)
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

end QueryCompatReplay

namespace QueryCompatReplay

def start (constants : Std.HashMap Name ConstantInfo) (base : Environment) : State := Id.run do
  let mut remaining : NameSet := {}
  for (name,ci) in constants.toList do
    if !ci.isUnsafe && !ci.isPartial then remaining := remaining.insert name
  return {env := base.toKernelEnv, remaining := remaining}

def runOwner (ctx : Context) (state : State) (names : Array Name) : IO State := do
  let (_, state) ← StateRefT'.run (s := state) do
    ReaderT.run (r := ctx) do
      for name in names do replayConstant name
      checkPostponedConstructors
      checkPostponedRecursors
  return state

end QueryCompatReplay

private def usedThroughOwnedHelpers (env : Environment)
 (owned : Std.HashMap Name ConstantInfo) (caller : Name) : Array Name := Id.run do
 let mut todo := #[caller]
 let mut seen : NameSet := {}
 let mut refs : NameSet := {}
 while !todo.isEmpty do
  let name := todo.back!
  todo := todo.pop
  if seen.contains name then continue
  seen := seen.insert name
  if let some ci := env.find? name then
   if let some value := ci.value? (allowOpaque := true) then
    for child in value.getUsedConstants do
     refs := refs.insert child
     if owned.contains child && !seen.contains child then todo := todo.push child
 return refs.toList.toArray
private def emit (message : String) : IO Unit := do
 let file ← IO.getStdout
 file.putStrLn message
 file.flush

def main (args : List String) : IO Unit := do
 let [file] := args | throw (IO.userError "expected config")
 let cfg : Config ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile file))
 initSearchPath (← findSysroot)
 emit "IMPORT_FULL_NEW_RAW_INVENTORY"
 let original ← importModules #[{module := cfg.entry.toName, importAll := true}] {} 0
  (loadExts := false) (level := .private)
 require (original.header.trustLevel == 0) "RAW_TRUST_NONZERO"
 let wanted := cfg.stages.foldl (fun names stage => names ++ stage.modules.map String.toName) #[]
 let mut owned : Std.HashMap Name ConstantInfo := {}
 for i in [:original.header.modules.size] do
  if wanted.contains original.header.modules[i]!.module then
   for ci in original.header.moduleData[i]!.constants do owned := owned.insert ci.name ci
 let mouths : Array (String × Array String × Bool) := #[("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromSplit",#["environment","source","before","after","request","split"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromRelationIndex",#["environment","source","occurrence","index"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.step",#["execution","index"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.reindex",#["original","target","language","same","execution"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth",#["factory","packet","prior","present","origin","index"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth_request_position",#["factory","packet","prior","present","origin","index"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth_segment_position",#["factory","packet","prior","present","origin","index"],false),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualBirth",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method"],true),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualStep_literal",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method","index"],true),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nativeNextReceipt",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method","index","item"],true),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method","index","item"],true),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_position",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method","index","item"],true),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_segment_position",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method","index","item"],true),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actual_next_receipt_completion",#["observation","nontrivial","half","depth","ordinal","Parent","Index","Whole","Next","HistoryEnd","History","update","cutoff","method","index","item"],true)]
 let mut mouthRows : Array Json := #[]
 for (name,expected,full) in mouths do
  let some ci := original.find? name.toName | throw (IO.userError s!"PUBLIC_MOUTH_MISSING {name}")
  let actual := binderNames ci.type
  let accepted := if full then actual == expected
   else expected.size ≤ actual.size && actual.extract (actual.size - expected.size) actual.size == expected
  require accepted s!"PUBLIC_BINDER_DRIFT {name}: {actual}"
  mouthRows := mouthRows.push <| Json.mkObj [("name",toJson name),("binders",toJson actual)]
 let direct := #[("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromSplit","written_trace"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromSplit","execution_split"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromSplit_before_length","List.length_append"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.relationPrefix","requestsFrom"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.relationPrefix","List.take"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.relationPrefix","WordReceipt.sourceRequest"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromRelationIndex","sourceRequestSplit"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromRelationIndex","fromSplit"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromRelationIndex","WordReceipt.sourceRequest"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromRelationIndex_before_length","fromSplit_before_length"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceInventoryExecutionFeed.ReceiptOccurrence.fromRelationIndex_before_length","List.get_idxOf"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.step","stepOccurrence"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.step","RelationOccurrence.transport"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.step_position","stepOccurrence_before_length"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.step_position","transport_position"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.boundary_written","Trace.relation_boundary"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.boundary_written","paid_boundary"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.boundary_written","stepOccurrence_word"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.boundary_written","transport_word"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.ExecutionAt.boundary_written","Submodule.subset_span"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","bornStock"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","born_inventory"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","stockDecodedEnvironment"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","decoded_environment"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","WordReceipt.sourceRequest"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","sourceItems"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","receipt"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth","fromRelationIndex"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth_request_position","source_before_length"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth_segment_position","fromRelationIndex_before_length"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ActualCofinalSourceAction.SourceReceiptOccurrence.atBirth_segment_position","stockDecodedEnvironment"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","bornStock"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","born_inventory"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","PhysicalGammaActionQuery.environment"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","decoded_environment"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","PhysicalGammaActionQuery.request"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","PhysicalGammaActionQuery.receipt"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.originalBirth","PhysicalGammaBoundaryFeedback.receiptSegment"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualBirth","reindex"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualBirth","born_packet_literal"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualBirth","originalBirth"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualStep_literal","reindex_step"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualStep_literal","originalBirth"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.following_literal","actual_next_packet"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nativeNextReceipt","atBirth"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nativeNextReceipt","actualStep"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nativeNextReceipt","actualBirth"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nativeNextReceipt","fixedRFactory"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt","reindex"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt","nativeNextReceipt"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt","following_literal"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_position","reindex_positions"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_position","atBirth_request_position"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_position","actualStep"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_segment_position","reindex_positions"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actualNextReceipt_segment_position","nativeNextReceipt"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nextReceiptRelation","actualNextReceipt"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nextReceiptRelation","relationFromExecution"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nextReceiptJointBoundary","jointFromRelation"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.nextReceiptJointBoundary","nextReceiptRelation"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actual_next_receipt_completion","completion_kills_generated_differential"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.actual_next_receipt_completion","nextReceiptJointBoundary"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.relationFromExecution","boundary_written"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.relationFromExecution","Finsupp.single"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.relationFromExecution","Expr.eval"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.jointFromRelation","liftMap"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.jointFromRelation","jointRelation_member"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRNativeGammaInstall.NextReceipt.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CountedPaInitial.BornRNativeGammaInstall.PhysicalGammaNextReceipt.jointFromRelation","jointHistoryAt")]
 let mut bindings : Array Json := #[]
 let mut referenceCache : Std.HashMap Name (Array Name) := {}
 for (caller,suffix) in direct do
  let callerName := caller.toName
  let refs := match referenceCache[callerName]? with
   | some refs => refs
   | none => usedThroughOwnedHelpers original owned callerName
  referenceCache := referenceCache.insert callerName refs
  let hits := refs.filter fun n => n.toString.endsWith suffix
  require (!hits.isEmpty) s!"DIRECT_SOURCE_BINDING_MISSING {caller}: {suffix}"
  bindings := bindings.push <| Json.mkObj [("caller",toJson caller),("callee_suffix",toJson suffix),("actual_callees",toJson (hits.map Name.toString))]
 let mut checkedModules : Array Name := #[]
 let mut allNames : Array Name := #[]
 let mut stageRows : Array Json := #[]
 let mut finalEnv := original
 for stage in cfg.stages do
  let modules := stage.modules.map String.toName
  emit s!"STAGE {stage.label}"
  let base ← importModules (stage.base.map fun n => ({module := n.toName, importAll := true} : Import)) {} 0
   (loadExts := false) (level := .private)
  unless modules.all (fun n => n.toString.startsWith "scratch.") do
   require (base.header.modules.all fun m => !m.module.toString.startsWith "scratch.")
    "PRODUCTION_BASE_HAS_SCRATCH"
  let unverified := wanted.filter fun n => !checkedModules.contains n
  let leaks := base.header.modules.filter fun m => unverified.contains m.module
  require leaks.isEmpty s!"UNVERIFIED_SOURCE_MODULE_LEAK {leaks.map (·.module)}"
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut owners : Std.HashMap Name Name := {}
  let mut names : Array Name := #[]
  let mut rows : Array Json := #[]
  let mut extras := 0
  let mut raw := 0
  let mut inherited := 0
  let mut duplicates := 0
  let mut rawModules : Array Json := #[]
  for i in [:original.header.modules.size] do
   let mod := original.header.modules[i]!.module
   unless modules.contains mod do continue
   let data := original.header.moduleData[i]!
   require (data.constNames == data.constants.map (·.name)) s!"BAD_RAW_INVENTORY {mod}"
   extras := extras + data.extraConstNames.size
   rawModules := rawModules.push <| Json.mkObj [("module",toJson mod.toString),
    ("selected_olean",toJson (← findOLean mod).toString),("raw",toJson data.constants.size),
    ("compiler_extras",toJson data.extraConstNames.size),("compiler_extra_names",toJson (data.extraConstNames.map Name.toString)),("imports",toJson (data.imports.map fun m => m.module.toString))]
   for ci in data.constants do
    raw := raw + 1
    let some actual := original.find? ci.name | throw (IO.userError s!"MISSING_RAW_CI {ci.name}")
    require (sameFullInfo ci actual) s!"RAW_CI_DIFFERENCE {ci.name}"
    require (!ci.isUnsafe && !ci.isPartial) s!"UNSAFE_OR_PARTIAL_NEW_CI {ci.name}"
    require (kind ci != "axiom") s!"NEW_AXIOM {ci.name}"
    require (!ci.getUsedConstantsAsSet.contains `sorryAx) s!"SORRY_DEPENDENCY {ci.name}"
    if let some previous := constants[ci.name]? then
     require (sameFullInfo ci previous) s!"REEMITTED_CI_DIFFERENCE {ci.name}"
     duplicates := duplicates + 1
     continue
    if let some previous := base.toKernelEnv.find? ci.name then
     require (sameFullInfo ci previous) s!"INHERITED_CI_DIFFERENCE {ci.name}"
     inherited := inherited + 1
     continue
    for dep in ci.getUsedConstantsAsSet do
     let some used := original.find? dep | throw (IO.userError s!"MISSING_DEPENDENCY {ci.name}: {dep}")
     require (!used.isUnsafe && !used.isPartial) s!"SAFE_TO_RUNTIME {ci.name}: {dep}"
    constants := constants.insert ci.name ci
    owners := owners.insert ci.name mod
    names := names.push ci.name
    rows := rows.push <| Json.mkObj [("name",toJson ci.name.toString),("owner",toJson mod.toString),("kind",toJson (kind ci)),
     ("binders",toJson (binderNames ci.type)),("value_dependencies",toJson ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[] |>.map Name.toString))]
  require (rawModules.size == modules.size) "NEW_SOURCE_MODULE_MISSING"
  require (inherited == 0) "INHERITED_SAFE_BODY_NEEDS_EXPLICIT_CHECK"
  let ctx : QueryCompatReplay.Context := {newConstants := constants, owners := owners, currentFile := System.FilePath.mk cfg.current, logFile := System.FilePath.mk cfg.progress}
  let before ← IO.monoMsNow
  let state ← QueryCompatReplay.runOwner ctx (QueryCompatReplay.start constants base) names
  for (name,ci) in constants.toList do
   let some value := state.env.find? name | throw (IO.userError s!"REPLAY_MISSING {name}")
   require (sameFullInfo ci value) s!"REPLAY_FULL_CI_DIFFERENCE {name}"
  finalEnv := Environment.ofKernelEnv state.env
  allNames := allNames ++ names
  checkedModules := checkedModules ++ modules
  let row := Json.mkObj [("label",toJson stage.label),("safe_private",toJson constants.size),
   ("raw",toJson raw),("compiler_runtime",toJson (#[] : Array Json)),("compiler_extras",toJson extras),("inherited",toJson inherited),("duplicates",toJson duplicates),
   ("replay_ms",toJson ((← IO.monoMsNow)-before)),("kernel_calls",toJson state.checkedCalls),
   ("base_has_unverified_sources",toJson false),("modules",toJson rawModules),("declarations",toJson rows)]
  stageRows := stageRows.push row
  IO.FS.writeFile (System.FilePath.mk cfg.output |>.parent.get! |>.join (stage.label ++ ".checked.json")) (row.pretty ++ "\n")
  emit s!"STAGE_CHECKED {stage.label} CIs={constants.size}"
 emit "TRANSITIVE_AXIOMS"
 let (used,closure) ← axioms finalEnv.toKernelEnv allNames
 require (used.all #[`propext,`Classical.choice,`Quot.sound].contains) s!"UNAUTHORIZED_AXIOM {used}"
 let report := Json.mkObj [("schema",toJson "r-cofinal-next-exposure-private-body-audit/v1"),
  ("accepted",toJson true),("axioms",toJson (used.map Name.toString)),("axiom_closure",toJson closure),
  ("safe_private_original_CIs",toJson allNames.size),("stages",toJson stageRows),
  ("public_mouths",toJson mouthRows),("source_body_bindings",toJson bindings)]
 IO.FS.writeFile cfg.output (report.pretty ++ "\n")
 emit s!"PASS new-safe-private={allNames.size}"
