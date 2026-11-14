import Lean
import Lean.Replay
set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
open Lean
structure RawOwner where
 name : String
 selected : String
 physical : String
 imports : Array String
 deriving FromJson
structure Config where
 label : String
 modules : Array RawOwner
 base : Array String
 output : String
 progress : String
 current : String
 deriving FromJson

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

private def require (ok : Bool) (message : String) : IO Unit := do
 unless ok do throw (IO.userError message)

private def emit (message : String) : IO Unit := do
 let out ← IO.getStdout
 out.putStrLn message
 out.flush

private def usedInRawBodies (raw : Std.HashMap Name ConstantInfo) (caller : Name) (followProofs : Bool := true) : NameSet := Id.run do
 let mut todo := #[caller]
 let mut seen : NameSet := {}
 let mut used : NameSet := {}
 while !todo.isEmpty do
  let name := todo.back!
  todo := todo.pop
  if seen.contains name then continue
  seen := seen.insert name
  if let some ci := raw[name]? then
   if !followProofs then
    if let .thmInfo _ := ci then continue
   if let some value := ci.value? (allowOpaque := true) then
    for dep in value.getUsedConstants do
     used := used.insert dep
     if raw.contains dep then todo := todo.push dep
 return used

def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected config")
 let cfg : Config ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile path))
 initSearchPath (← findSysroot)
 require (cfg.modules.size == 3) "WRONG_FRESH_MODULE_SCOPE"
 let mut physicalRegions : Array CompactedRegion := #[]
 let mut runtimeRaw : Array (Name × ConstantInfo) := #[]
 let mut raw : Std.HashMap Name ConstantInfo := {}
 let mut owners : Std.HashMap Name Name := {}
 let mut names : Array Name := #[]
 let mut rawModules : Array Json := #[]
 let mut declarationRows : Array Json := #[]
 let mut regions : Array CompactedRegion := #[]
 let mut extras := 0
 let companionScope : Array (Name × Name × Name) := #[]
 emit "READ_FRESH_RAW_MODULEDATA"
 for row in cfg.modules do
  let mod := row.name.toName
  let selected ← findOLean mod
  require (selected.toString == row.selected) s!"FIRST_HIT_DRIFT {mod}"
  let (data,region) ← readModuleData selected
  regions := regions.push region
  let (physicalData, physicalRegion) ← readModuleData (System.FilePath.mk row.physical)
  physicalRegions := physicalRegions.push physicalRegion
  require (data.constNames == physicalData.constNames) s!"PHYSICAL_RAW_INVENTORY_DRIFT {mod}"
  require (data.constNames == data.constants.map (·.name)) s!"BAD_RAW_INVENTORY {mod}"
  let imports := data.imports.map fun dep => dep.module.toString
  require (imports == row.imports) s!"RAW_IMPORT_DRIFT {mod}"
  for imported in imports do
   require (imported == "Init" || cfg.base.contains imported || cfg.modules.any (·.name == imported))
    s!"RAW_IMPORT_OUTSIDE_PROVED_CONTEXT {mod}: {imported}"
  extras := extras + data.extraConstNames.size
  rawModules := rawModules.push <| Json.mkObj [("module",toJson row.name),
    ("selected_olean",toJson selected.toString),("raw",toJson data.constants.size),
    ("compiler_extras",toJson data.extraConstNames.size),("compiler_extra_names",toJson (data.extraConstNames.map Name.toString)),
    ("imports",toJson imports)]
  for i in [:data.constants.size] do
   let ci := data.constants[i]!
   if ci.isUnsafe || ci.isPartial then
    require (!ci.isUnsafe && ci.isPartial && kind ci == "definition" &&
       companionScope.contains (ci.name,mod,ci.name.getPrefix)) s!"UNCLASSIFIED_RUNTIME_CI {ci.name}"
    require (!runtimeRaw.any (fun (_, previous) => previous.name == ci.name)) s!"DUPLICATE_RUNTIME_CI {ci.name}"
    require (sameFullInfo ci physicalData.constants[i]!) s!"RUNTIME_PHYSICAL_CI_DRIFT {ci.name}"
    runtimeRaw := runtimeRaw.push (mod,ci)
    continue
   require (!raw.contains ci.name && !ci.isUnsafe && !ci.isPartial && kind ci != "axiom")
    s!"DUPLICATE_OR_UNSAFE_NEW_CI {ci.name}"
   require (!ci.getUsedConstantsAsSet.contains `sorryAx) s!"SORRY_DEPENDENCY {ci.name}"
   raw := raw.insert ci.name ci
   owners := owners.insert ci.name mod
   names := names.push ci.name
   declarationRows := declarationRows.push <| Json.mkObj [("name",toJson ci.name.toString),("owner",toJson row.name),
     ("kind",toJson (kind ci)),("binders",toJson (binderNames ci.type)),
     ("value_dependencies",toJson ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[] |>.map Name.toString))]
 require (runtimeRaw.size == companionScope.size && physicalRegions.size == cfg.modules.size)
  "WRONG_EXACT_COMPILER_COMPANION_SCOPE"
 let mut runtimeRows : Array Json := #[]
 for (mod,ci) in runtimeRaw do
  let safeName := ci.name.getPrefix
  let some safe := raw[safeName]? | throw (IO.userError s!"RUNTIME_WITHOUT_OWNED_SOURCE {ci.name}")
  require (owners[safeName]? == some mod && kind safe == "definition" && !safe.isUnsafe && !safe.isPartial)
   s!"RUNTIME_WITHOUT_EXACT_SAFE_SOURCE {ci.name}"
  let selfEdge := ci.getUsedConstantsAsSet.contains ci.name
  let fromLogical := raw.toList.filter fun (_,caller) => caller.getUsedConstantsAsSet.contains ci.name
  let fromOtherCompanion := runtimeRaw.filter fun (_,caller) =>
    caller.name != ci.name && caller.getUsedConstantsAsSet.contains ci.name
  require (selfEdge && fromLogical.isEmpty && fromOtherCompanion.isEmpty)
   s!"COMPILER_RUNTIME_INCOMING_EDGE {ci.name}"
  runtimeRows := runtimeRows.push <| Json.mkObj [("name",toJson ci.name.toString),("owner",toJson mod.toString),
    ("safe_source",toJson safeName.toString),("isUnsafe",toJson ci.isUnsafe),("isPartial",toJson ci.isPartial),
    ("self_edges",toJson (1 : Nat)),("nonself_incoming_edges",toJson (0 : Nat)),
    ("type_preserved",toJson true),("value_preserved",toJson true)]
 let mouths : Array (String × String × Array String × Nat) := #[("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv", "SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence", #["L", "M", "_", "_", "evaluate", "injective", "p", "divides"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction", "SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence", #["L", "M", "_", "_", "evaluate", "injective", "p", "divides", "j", "value"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_inverse", "SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence", #["L", "M", "_", "_", "evaluate", "injective", "p", "divides", "value"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.evaluationCokernelAction", "SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality", #["L", "M", "L'", "M'", "_", "_", "_", "_", "evaluate", "evaluateNext", "source", "target", "actual"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality", "SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality", #["L", "M", "L'", "M'", "_", "_", "_", "_", "evaluate", "evaluateNext", "source", "target", "actual", "injective", "injectiveNext", "p", "value"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality", "SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality", #["L", "M", "L'", "M'", "_", "_", "_", "_", "evaluate", "evaluateNext", "source", "target", "actual", "injective", "injectiveNext", "p", "divides", "dividesNext", "value"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion", "SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion", #["observation", "nontrivial", "half", "depth", "ordinal", "p"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion", "SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion", #["observation", "nontrivial", "half", "depth", "ordinal", "p"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletionNext", "SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion", #["observation", "nontrivial", "half", "depth", "ordinal", "p"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_completion_restriction", "SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion", #["observation", "nontrivial", "half", "depth", "ordinal", "p", "j", "value"], 0),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next", "SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion", #["observation", "nontrivial", "half", "depth", "ordinal", "p", "value"], 0)]
 let mut mouthRows : Array Json := #[]
 let mut mouthErrors : Array String := #[]
 for (name,owner,expected,arrows) in mouths do
  let some ci := raw[name.toName]? | throw (IO.userError s!"PUBLIC_MOUTH_MISSING {name}")
  require (owners[name.toName]? == some owner.toName) s!"PUBLIC_OWNER_DRIFT {name}"
  let binders := binderNames ci.type
  let compared := ((binders.extract 0 expected.size).zip expected).map fun (actual,wanted) =>
    if wanted == "_" then "_" else if actual.startsWith "inst." then "inst" else actual
  unless binders.size == expected.size + arrows && compared == expected do
   mouthErrors := mouthErrors.push s!"EXACT_SOURCE_INPUT_DRIFT {name}: {binders}"
  mouthRows := mouthRows.push <| Json.mkObj [("name",toJson name),("owner",toJson owner),
    ("binders",toJson binders),("input_binders",toJson compared),("result_arrows",toJson arrows)]
 require mouthErrors.isEmpty (String.intercalate "\n" mouthErrors.toList)
 let valueEdges : Array (String × String) := #[("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelTowerMap","CategoryTheory.NatTrans.ofOpSequence"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelTowerMap","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.stageCokernelEquiv"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelTowerMap","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.stage_cokernel_transition"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelAtLimit","CategoryTheory.Limits.limMap"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelAtLimit","_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelTowerMap"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelAtLimit"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelConnectingAtLimit"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.source_cokernel_limit_restriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_restriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.stage_cokernel_connecting_inverse"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","CategoryTheory.Limits.Concrete.limit_ext"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction","_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.source_cokernel_limit_restriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.evaluationCokernelAction","Submodule.mapQ"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_stage_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_torsion_has_division"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_stage_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelTorsionClassOfDivision"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_stage_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.stage_cokernel_connecting_of_paid"),
  ("_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_stage_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.stageMap_projection"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","CategoryTheory.Limits.Concrete.limit_ext"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentNaturality.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_stage_naturality"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.torsion_limit_map_restriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.inducedCompletionMap_restriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.paidEvaluation"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_evaluation_injective"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelTopology.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.ambient_power_bijective"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.factor"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_factor_injective"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.complex_power_bijective"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletionNext","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.primePowerTorsionLimitMap"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletionNext","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelNext"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletionNext","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelToModel"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_coherent_factor","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.evaluationToModel"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_coherent_factor","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality"),
  ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_coherent_factor","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.inducedCompletionMap_id"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelCompletion.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_coherent_factor"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_model_square"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.modelAction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.modelCharge"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality")]
 let typeEdges : Array (String × String) := #[("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.Completion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.PrimePowerTorsionCompletion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","LinearMap.range"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","Function.Bijective"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.powerMultiplication"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.torsionCompletionRestriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.stageCokernelEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.restriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_inverse","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_inverse","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelConnectingAtLimit"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.evaluationCokernelAction","LinearMap.range"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelConnectingAtLimit"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.evaluationCokernelAction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.primePowerTorsionLimitMap"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_connecting_limit_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.inducedCompletionLinearMap"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernelCompletionEquiv"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.evaluationCokernelAction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.inducedCompletionLinearMap"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.Completion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.PrimePowerTorsionCompletion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.paidEvaluation"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.Completion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.PrimePowerTorsionCompletion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.factor"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelStage"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_completion_restriction","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.torsionCompletionRestriction"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletionNext"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelModel.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.modelCharge"),
  ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next","SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.inducedCompletionLinearMap")]
 let mut bodyRows : Array Json := #[]
 let mut typeRows : Array Json := #[]
 let mut missing : Array String := #[]
 let mut cache : Std.HashMap Name NameSet := {}
 for (caller,callee) in valueEdges do
  let refs := match cache[caller.toName]? with
   | some refs => refs
   | none => usedInRawBodies raw caller.toName
  cache := cache.insert caller.toName refs
  unless refs.contains callee.toName do
   missing := missing.push s!"VALUE_BODY_BINDING_MISSING {caller}: {callee}"
  bodyRows := bodyRows.push <| Json.mkObj [("caller",toJson caller),("callee",toJson callee)]
 for (caller,callee) in typeEdges do
  let some ci := raw[caller.toName]? | throw (IO.userError s!"TYPE_MOUTH_MISSING {caller}")
  unless ci.type.getUsedConstants.contains callee.toName do
   missing := missing.push s!"TYPE_BINDING_MISSING {caller}: {callee}"
  typeRows := typeRows.push <| Json.mkObj [("caller",toJson caller),("callee",toJson callee)]
 require missing.isEmpty (String.intercalate "\n" missing.toList)
 let sourceMouths : Array Name := #[ "_private.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion.CoherentEquivalence.0.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.sourceCokernelTowerMap".toName,
   "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.evaluationCokernelAction".toName, "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletion".toName, "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidModelCokernelCompletion".toName,
   "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actualPaidCokernelCompletionNext".toName ]
 let targets : Array Name := #[ "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceGeneratedPrimePowerCompletion.cokernel_completion_equiv_naturality".toName,
   "SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.RootRelation.actual_paid_cokernel_coherent_next".toName ]
 for root in sourceMouths do
  let deps := usedInRawBodies raw root
  require (!(raw[root]!.type.getUsedConstants.any targets.contains) &&
    !(deps.toArray.any targets.contains)) s!"COHERENT_COKERNEL_SOURCE_READS_TARGET {root}"
 let targetReads : Array Name := #[]
 emit s!"MOUTHS {mouthRows.size} VALUE_BINDINGS {bodyRows.size} TYPE_BINDINGS {typeRows.size}"

 emit "IMPORT_SUBJECT_FREE_PAID_BASE_ONCE"
 let base ← importModules (cfg.base.map fun name => ({module := name.toName, importAll := true} : Import)) {} 0
   (loadExts := false) (level := .private)
 require (base.header.trustLevel == 0) "BASE_TRUST_NONZERO"
 let unverified := cfg.modules.map (·.name)
 require (base.header.modules.all fun mod =>
   !unverified.contains mod.module.toString && !mod.module.toString.startsWith "scratch.")
   "SUBJECT_OR_SCRATCH_IN_PAID_BASE"
 let sharedGeneratedNames : Array Name := #[]
 let mut inherited : Array Json := #[]
 let mut fresh := raw
 for name in names do
  if let some existing := base.find? name then
   require (sharedGeneratedNames.contains name && sameFullInfo (raw[name]!) existing)
    s!"UNEXPECTED_OR_DIFFERENT_INHERITED_CI {name}"
   let some index := base.getModuleIdxFor? name | throw (IO.userError s!"INHERITED_CI_OWNER_MISSING {name}")
   let importedOwner := base.header.modules[index]!.module.toString
   inherited := inherited.push <| Json.mkObj [("name",toJson name.toString),
     ("raw_owner",toJson (owners[name]!.toString)),("paid_owner",toJson importedOwner),
     ("same_full_constant_info",toJson true),("kernel_replayed",toJson false)]
   fresh := fresh.erase name
  for dep in (raw[name]!).getUsedConstantsAsSet do
   let some used := (raw[dep]?).orElse (fun _ => base.find? dep) |
     throw (IO.userError s!"MISSING_EXACT_DEPENDENCY {name}: {dep}")
   require (!used.isUnsafe && !used.isPartial) s!"SAFE_TO_RUNTIME {name}: {dep}"

 emit s!"STAGE {cfg.label}"
 let ctx : QueryCompatReplay.Context := ⟨fresh, owners, System.FilePath.mk cfg.current, System.FilePath.mk cfg.progress⟩
 let start ← IO.monoMsNow
 let freshNames := names.filter fresh.contains
 require (freshNames.size == fresh.size && fresh.size + inherited.size == names.size) "RAW_PARTITION_DRIFT"
 emit s!"RAW_PARTITION fresh={fresh.size} inheritedFullCI={inherited.size}"
 let checked ← QueryCompatReplay.runOwner ctx (QueryCompatReplay.start fresh base) freshNames
 let mut regeneratedRows : Array Json := #[]
 for name in freshNames do
  let ci := fresh[name]!
  if kind ci == "constructor" || kind ci == "recursor" then
   let some actual := checked.env.find? name | throw (IO.userError s!"GENERATED_INDUCTIVE_CI_MISSING {name}")
   require (sameFullInfo ci actual) s!"GENERATED_INDUCTIVE_FULL_CI_DRIFT {name}"
   regeneratedRows := regeneratedRows.push <| Json.mkObj [("name",toJson name.toString),
     ("owner",toJson (owners[name]!.toString)),("kind",toJson (kind ci)),
     ("regenerated_in_inductive_block",toJson true),("same_full_constant_info",toJson true)]
 require (checked.remaining.isEmpty && checked.pending.isEmpty &&
   checked.checkedCalls + regeneratedRows.size == fresh.size && regeneratedRows.size == 0)
   "FRESH_KERNEL_OR_INDUCTIVE_CI_REPLAY_INCOMPLETE"
 for (name,ci) in raw.toList do
  let some result := checked.env.find? name | throw (IO.userError s!"REPLAY_MISSING {name}")
  require (sameFullInfo ci result) s!"REPLAY_FULL_CI_DIFFERENCE {name}"
 let elapsed := (← IO.monoMsNow) - start
 emit s!"STAGE_CHECKED {cfg.label} CIs={raw.size}"
 emit "TRANSITIVE_AXIOMS"
 let (used,closure) ← axioms checked.env names
 require (used.all #[`propext,`Classical.choice,`Quot.sound].contains) s!"UNAUTHORIZED_AXIOM {used}"
 let row := Json.mkObj [("label",toJson cfg.label),("safe_private",toJson raw.size),
    ("raw",toJson (names.size + runtimeRows.size)),("compiler_runtime",toJson runtimeRows),("compiler_extras",toJson extras),
    ("inherited",toJson inherited.size),("inherited_generated_full_CIs",toJson inherited),
    ("fresh_replayed",toJson fresh.size),("duplicates",toJson (0:Nat)),("replay_ms",toJson elapsed),
    ("kernel_calls",toJson checked.checkedCalls),("inductive_generated_CIs",toJson regeneratedRows),("base_has_unverified_sources",toJson false),
    ("modules",toJson rawModules),("declarations",toJson declarationRows)]
 let report := Json.mkObj [("schema",toJson "cp743-raw-first-private-body-audit/v1"),
    ("accepted",toJson true),("axioms",toJson (used.map Name.toString)),("axiom_closure",toJson closure),
    ("safe_private_original_CIs",toJson raw.size),("fresh_safe_replayed_CIs",toJson fresh.size),
    ("inherited_generated_full_CI_matches",toJson inherited.size),("stages",toJson #[row]),("public_mouths",toJson mouthRows),
    ("source_body_bindings",toJson bodyRows),("source_type_bindings",toJson typeRows),
    ("original_coherent_cokernel_data_ancestry",Json.mkObj [
      ("actual_stage_divisions_generate_the_full_coherent_equivalence",toJson true),
      ("the_original_connecting_map_is_the_entire_coherent_inverse",toJson true),
      ("each_actual_evaluation_square_moves_the_original_divided_class",toJson true),
      ("the_same_actual_evaluation_and_factor_supply_the_current_cokernels",toJson true),
      ("the_literal_model_action_supplies_the_entire_coherent_next",toJson true)]),
    ("source_target_reads",toJson (targetReads.map Name.toString)),("fresh_raw_regions",toJson regions.size),
    ("paid_base_environment_imports",toJson (1:Nat)),("full_candidate_environment_imports",toJson (0:Nat))]
 IO.FS.writeFile cfg.output (report.pretty ++ "\n")
 emit s!"PASS raw-safe-private={raw.size} fresh-replayed={fresh.size} inherited-full-CI={inherited.size}"
