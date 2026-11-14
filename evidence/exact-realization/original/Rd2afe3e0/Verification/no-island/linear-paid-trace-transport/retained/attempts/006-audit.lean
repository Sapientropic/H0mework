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
 count : Nat
 privateCount : Nat
 extras : Array String
 names : Array String
 runtime : Array String
 deriving FromJson

structure Config where
 modules : Array RawOwner
 base : Array String
 output : String
 progress : String
 current : String
 mouths : Array (String × String × Array String)
 bodyEdges : Array (String × String)
 typeEdges : Array (String × String)
 exclusions : Array (String × Array String)
 inherited : Array String
 paidSelected : Array (String × String)
 paidSource : Array (String × String × String × String × Array String × Array String)
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
private structure AxiomGraph where
 parents : Std.HashMap Name (Array Name)
 axioms : Array Name
 closure : Nat

/-- Scan each stored type and body once, retaining the reverse edges for axiom attribution. -/
private def axiomGraph (env : Kernel.Environment) (roots : Array Name) : IO AxiomGraph := do
 let mut todo := roots
 let mut seen : NameSet := {}
 let mut parents : Std.HashMap Name (Array Name) := {}
 let mut found : NameSet := {}
 while !todo.isEmpty do
  let name := todo.back!
  todo := todo.pop
  if seen.contains name then continue
  seen := seen.insert name
  let some ci := env.find? name | throw (IO.userError s!"MISSING_AXIOM_DEPENDENCY {name}")
  if let .axiomInfo _ := ci then found := found.insert name
  for child in ci.getUsedConstantsAsSet do
   parents := parents.alter child (fun row => some ((row.getD #[]).push name))
   unless seen.contains child do todo := todo.push child
 return ⟨parents,found.toList.toArray,seen.size⟩

/-- Reverse reachability attributes an axiom exactly, including through cyclic declarations. -/
private def axiomUsers (graph : AxiomGraph) (axiomName : Name) : NameSet := Id.run do
 let mut todo := #[axiomName]
 let mut seen : NameSet := {}
 while !todo.isEmpty do
  let name := todo.back!
  todo := todo.pop
  if seen.contains name then continue
  seen := seen.insert name
  for parent in graph.parents.getD name #[] do
   unless seen.contains parent do todo := todo.push parent
 return seen

private def binderNames (e : Expr) : Array String := Id.run do
 let mut e := e
 let mut out := #[]
 while true do
  match e with
  | .forallE n _ body _ =>
   out := out.push n.toString
   e := body
  | .letE _ _ _ body _ | .mdata _ body => e := body
  | _ => break
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

private def usedInRawBodies (raw : Std.HashMap Name ConstantInfo) (caller : Name) : NameSet := Id.run do
 let mut todo := #[caller]
 let mut seen : NameSet := {}
 let mut used : NameSet := {}
 while !todo.isEmpty do
  let name := todo.back!
  todo := todo.pop
  if seen.contains name then continue
  seen := seen.insert name
  if let some ci := raw[name]? then
   if let some value := ci.value? (allowOpaque := true) then
    for dep in value.getUsedConstants do
     used := used.insert dep
     if raw.contains dep then todo := todo.push dep
 return used

private def hasSuffix (dependencies : Array Name) (suffix : String) : Bool :=
 dependencies.any fun dep => dep.toString == suffix || dep.toString.endsWith ("." ++ suffix)

private def checkBinderNames (actual expected : Array String) : Bool :=
 actual.size == expected.size && (actual.zip expected).all (fun (a,b) => b == "_" || a == b)

def main (args : List String) : IO Unit := do
 let [path] := args | throw (IO.userError "expected one config")
 let cfg : Config ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile path))
 initSearchPath (← findSysroot)
 require (cfg.modules.size == 4 && !cfg.base.isEmpty) "WRONG_NEW_MODULE_SCOPE"
 let mut regions : Array CompactedRegion := #[]
 let mut raw : Std.HashMap Name ConstantInfo := {}
 let mut runtime : Std.HashMap Name ConstantInfo := {}
 let mut runtimeRows : Array Json := #[]
 let mut owners : Std.HashMap Name Name := {}
 let mut names : Array Name := #[]
 let mut moduleRows : Array Json := #[]
 let mut extraNames : Array Name := #[]
 let mut declarations : Array Json := #[]
 emit "READ_FRESH_RAW_MODULEDATA"
 for row in cfg.modules do
  let mod := row.name.toName
  let selected ← findOLean mod
  require (selected.toString == row.selected) s!"FIRST_HIT_DRIFT {mod}"
  let (data,region) ← readModuleData selected
  let (physical,physicalRegion) ← readModuleData (System.FilePath.mk row.physical)
  regions := regions.push region |>.push physicalRegion
  let imports := data.imports.map fun dep => dep.module.toString
  require (!data.isModule && data.constNames == data.constants.map (·.name) &&
    data.constNames == physical.constNames && data.imports == physical.imports &&
    data.constants.size == row.count && physical.constants.size == row.count &&
    data.constNames.map Name.toString == row.names && imports == row.imports &&
    data.extraConstNames == physical.extraConstNames && data.extraConstNames.map Name.toString == row.extras)
    s!"RAW_INVENTORY_OR_IMPORT_DRIFT {mod}"
  for imported in imports do
   require (imported == "Init" || cfg.base.contains imported || cfg.modules.any (·.name == imported))
     s!"IMPORT_OUTSIDE_SCOPE {mod}: {imported}"
  extraNames := extraNames ++ data.extraConstNames
  let mut privateCount := 0
  let mut runtimeCount := 0
  for (ci,other) in data.constants.zip physical.constants do
   require (sameFullInfo ci other && !raw.contains ci.name && !runtime.contains ci.name && !ci.isUnsafe &&
     !ci.getUsedConstantsAsSet.contains `sorryAx) s!"INVALID_RAW_CI {ci.name}"
   if isPrivateName ci.name then privateCount := privateCount + 1
   owners := owners.insert ci.name mod
   if row.runtime.contains ci.name.toString then
    require (ci.isPartial && isPrivateName ci.name && kind ci == "definition" &&
      (ci.name.toString.endsWith ".tallyContext._unsafe_rec" || ci.name.toString.endsWith ".tallyCochain._unsafe_rec"))
      s!"UNCLASSIFIED_COMPILER_RUNTIME_CI {ci.name}"
    runtime := runtime.insert ci.name ci
    runtimeCount := runtimeCount + 1
   else
    require (!ci.isPartial && (kind ci == "definition" || kind ci == "theorem" || kind ci == "opaque"))
      s!"INVALID_LOGICAL_CI {ci.name}"
    raw := raw.insert ci.name ci
    names := names.push ci.name
    declarations := declarations.push <| Json.mkObj [("name",toJson ci.name.toString),("owner",toJson row.name),
      ("kind",toJson (kind ci)),("binders",toJson (binderNames ci.type)),
      ("type_dependencies",toJson (ci.type.getUsedConstants.map Name.toString)),
      ("body_dependencies",toJson (((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[] |>.map Name.toString))]
  require (privateCount == row.privateCount && runtimeCount == row.runtime.size) s!"PRIVATE_OR_RUNTIME_INVENTORY_DRIFT {mod}"
  moduleRows := moduleRows.push <| Json.mkObj [("module",toJson row.name),("selected",toJson selected.toString),
    ("imports",toJson imports),("raw",toJson row.count),("logical",toJson (row.count-runtimeCount)),
    ("private",toJson (privateCount-runtimeCount)),("raw_private",toJson privateCount),
    ("compiler_runtime_names",toJson row.runtime),("compiler_extra_names",toJson row.extras)]
 require (raw.size == names.size && raw.size == 74 && runtime.size == 2 && regions.size == 2 * cfg.modules.size)
   "RAW_OWNER_SCOPE_DRIFT"
 let extraSet := extraNames.foldl (fun (set : NameSet) name => set.insert name) {}
 require (extraSet.size == extraNames.size && extraNames.size == 773) "COMPILER_EXTRA_COUNT_DRIFT"
 for (name,ci) in raw.toList do
  require (!extraSet.contains name && (ci.getUsedConstantsAsSet.toList.all fun dep =>
    !extraSet.contains dep && !runtime.contains dep)) s!"LOGICAL_DEPENDENCY_ON_COMPILER_ARTIFACT {name}"
 for (name,ci) in runtime.toList do
  let parent := name.getPrefix
  let some owner := owners[name]? | throw (IO.userError s!"RUNTIME_OWNER_MISSING {name}")
  let some logicalParent := raw[parent]? | throw (IO.userError s!"RUNTIME_LOGICAL_PARENT_MISSING {parent}")
  require (owners[parent]? == some owner && kind logicalParent == "definition" && !extraSet.contains name)
    s!"RUNTIME_PARENT_DRIFT {name}"
  let incoming := runtime.toList.filter (fun (_,other) => other.getUsedConstantsAsSet.contains name)
  require (incoming.map Prod.fst == [name]) s!"RUNTIME_INCOMING_NOT_SELF_ONLY {name}"
  runtimeRows := runtimeRows.push <| Json.mkObj [("name",toJson name.toString),("owner",toJson owner.toString),
    ("parent",toJson parent.toString),("kind",toJson (kind ci)),("partial",toJson ci.isPartial),
    ("unsafe",toJson ci.isUnsafe),("incoming",toJson (#[name.toString]))]
 let mut mouths : Array Json := #[]
 let mut mouthErrors : Array String := #[]
 for (name,owner,expected) in cfg.mouths do
  let some ci := raw[name.toName]? | throw (IO.userError s!"MOUTH_MISSING {name}")
  require (owners[name.toName]? == some owner.toName) s!"MOUTH_OWNER_DRIFT {name}"
  let binders := binderNames ci.type
  unless checkBinderNames binders expected do
   mouthErrors := mouthErrors.push s!"BINDER_DRIFT {name}: {binders} expected {expected}"
  mouths := mouths.push <| Json.mkObj [("name",toJson name),("owner",toJson owner),("binders",toJson binders)]
 require mouthErrors.isEmpty (String.intercalate "\n" mouthErrors.toList)
 let mut missing : Array String := #[]
 for (caller,callee) in cfg.bodyEdges do
  let some ci := raw[caller.toName]? | throw (IO.userError s!"MISSING_BODY_OWNER {caller}")
  let some value := ci.value? (allowOpaque := true) | throw (IO.userError s!"MISSING_BODY {caller}")
  unless value.getUsedConstants.contains callee.toName do
   missing := missing.push s!"BODY_EDGE_MISSING {caller}: {callee}"
 for (caller,callee) in cfg.typeEdges do
  let some ci := raw[caller.toName]? | throw (IO.userError s!"MISSING_TYPE_OWNER {caller}")
  unless ci.type.getUsedConstants.contains callee.toName do
   missing := missing.push s!"TYPE_EDGE_MISSING {caller}: {callee}"
 require missing.isEmpty (String.intercalate "\n" missing.toList)
 for (root,targets) in cfg.exclusions do
  let some ci := raw[root.toName]? | throw (IO.userError s!"MISSING_SOURCE_ROOT {root}")
  let body := usedInRawBodies raw root.toName
  require (targets.all fun target => !body.contains target.toName && !ci.type.getUsedConstants.contains target.toName)
    s!"SOURCE_USES_DOWNSTREAM_TARGET {root}"
 emit s!"MOUTHS {mouths.size} BODY_EDGES {cfg.bodyEdges.size} TYPE_EDGES {cfg.typeEdges.size} RUNTIME {runtimeRows.size}"
 let mut paidSelected : Array Json := #[]
 for (name,expected) in cfg.paidSelected do
  let actual ← findOLean name.toName
  require (actual.toString == expected) s!"PAID_FIRST_HIT_DRIFT {name}"
  paidSelected := paidSelected.push <| Json.mkObj [("module",toJson name),("selected",toJson actual.toString)]
 let mut paidCIs : Array Json := #[]
 let mut paidErrors : Array String := #[]
 let mut paidModules : Std.HashMap Name ModuleData := {}
 for (owner,expected,name,expectedKind,typeEdges,bodyEdges) in cfg.paidSource do
  let hit ← findOLean owner.toName
  require (hit.toString == expected) s!"PAID_CI_OWNER_DRIFT {owner}"
  let ownerName := owner.toName
  unless paidModules.contains ownerName do
   let (data,region) ← readModuleData hit
   paidModules := paidModules.insert ownerName data
   regions := regions.push region
  let matching := (paidModules[ownerName]!).constants.filter (·.name.toString == name)
  let some ci := matching[0]? | throw (IO.userError s!"MISSING_PAID_SOURCE_CI {name}")
  let some value := ci.value? (allowOpaque := true) | throw (IO.userError s!"MISSING_PAID_SOURCE_VALUE {name}")
  require (matching.size == 1 && !ci.isUnsafe && !ci.isPartial && kind ci == expectedKind) s!"PAID_CI_KIND_DRIFT {name}"
  for edge in typeEdges do
   unless hasSuffix ci.type.getUsedConstants edge do
    paidErrors := paidErrors.push s!"PAID_TYPE_EDGE_MISSING {name}: {edge}"
  for edge in bodyEdges do
   unless hasSuffix value.getUsedConstants edge do
    paidErrors := paidErrors.push s!"PAID_BODY_EDGE_MISSING {name}: {edge}"
  paidCIs := paidCIs.push <| Json.mkObj [("name",toJson ci.name.toString),("owner",toJson owner),
    ("selected",toJson hit.toString),("kind",toJson expectedKind),("type_edges",toJson typeEdges),
    ("body_edges",toJson bodyEdges)]
 require paidErrors.isEmpty (String.intercalate "\n" paidErrors.toList)
 emit s!"EXACT_PAID_IMPORTS {paidSelected.size} PAID_SOURCE_CIS {paidCIs.size}"
 emit "IMPORT_SUBJECT_FREE_PAID_BASE_ONCE"
 let base ← importModules (cfg.base.map fun name => ({module := name.toName, importAll := true} : Import)) {} 0
   (loadExts := false) (level := .private)
 require (base.header.trustLevel == 0) "BASE_TRUST_NONZERO"
 let unverified := cfg.modules.map (·.name)
 require (base.header.modules.all fun mod =>
   !unverified.contains mod.module.toString && !mod.module.toString.startsWith "scratch.")
   "SUBJECT_OR_SCRATCH_IN_PAID_BASE"
 let mut inherited : Array Json := #[]
 let mut fresh := raw
 for name in names do
  if let some existing := base.find? name then
   require (cfg.inherited.contains name.toString && sameFullInfo (raw[name]!) existing)
     s!"UNEXPECTED_OR_DIFFERENT_INHERITED_CI {name}"
   let some index := base.getModuleIdxFor? name | throw (IO.userError s!"INHERITED_CI_OWNER_MISSING {name}")
   inherited := inherited.push <| Json.mkObj [("name",toJson name.toString),
     ("raw_owner",toJson (owners[name]!.toString)),("paid_owner",toJson base.header.modules[index]!.module.toString),
     ("same_full_CI",toJson true)]
   fresh := fresh.erase name
  for dep in (raw[name]!).getUsedConstantsAsSet do
   let some used := (raw[dep]?).orElse (fun _ => base.find? dep) | throw (IO.userError s!"MISSING_EXACT_DEPENDENCY {name}: {dep}")
   require (!used.isUnsafe && !used.isPartial) s!"SAFE_TO_RUNTIME {name}: {dep}"
 let freshNames := names.filter fresh.contains
 require (freshNames.size == fresh.size && fresh.size + inherited.size == names.size &&
   inherited.size == cfg.inherited.size) "RAW_PARTITION_DRIFT"
 let context : QueryCompatReplay.Context := ⟨fresh,owners,System.FilePath.mk cfg.current,System.FilePath.mk cfg.progress⟩
 emit s!"RAW_PARTITION fresh={fresh.size} inheritedFullCI={inherited.size}"
 let started ← IO.monoMsNow
 let checked ← QueryCompatReplay.runOwner context (QueryCompatReplay.start fresh base) freshNames
 let elapsed := (← IO.monoMsNow) - started
 require (checked.remaining.isEmpty && checked.pending.isEmpty && checked.checkedCalls == fresh.size)
   "INCOMPLETE_KERNEL_REPLAY"
 for (name,ci) in raw.toList do
  let some value := checked.env.find? name | throw (IO.userError s!"REPLAY_CI_MISSING {name}")
  require (sameFullInfo ci value) s!"REPLAY_FULL_CI_DRIFT {name}"
 emit s!"FRESH_KERNEL_REPLAY {checked.checkedCalls}"
 let graph ← axiomGraph checked.env names
 let used := graph.axioms
 let closure := graph.closure
 for (name,_) in runtime.toList do
  require ((checked.env.find? name).isNone) s!"COMPILER_RUNTIME_ENTERED_LOGICAL_ENV {name}"
 require (used.size == 3 && used.all #[`propext,`Classical.choice,`Quot.sound].contains) s!"UNEXPECTED_AXIOM_SET {used}"
 let uses := used.map (axiomUsers graph)
 let mut publicAxioms : Array Json := #[]
 for (name,_,_) in cfg.mouths do
  let mouthAxioms := (used.zip uses).filterMap fun (axiomName,users) =>
   if users.contains name.toName then some axiomName.toString else none
  publicAxioms := publicAxioms.push <| Json.mkObj [("name",toJson name),("axioms",toJson mouthAxioms)]
 let report := Json.mkObj [("schema",toJson "cp806-raw-first-private-body-audit/v1"),
    ("accepted",toJson true),("axioms",toJson (used.map Name.toString)),("axiom_closure",toJson closure),
    ("public_mouth_axioms",toJson publicAxioms),("raw_CIs",toJson (raw.size+runtime.size)),
    ("logical_CIs",toJson raw.size),("compiler_runtime_CIs",toJson runtimeRows),
    ("source_exclusions",toJson cfg.exclusions),
    ("axiom_traversal",toJson "single-forward-scan-reverse-reachability"),
    ("kernel_calls",toJson checked.checkedCalls),("replay_ms",toJson elapsed),("inherited_full_CIs",toJson inherited),
    ("compiler_extras",toJson extraNames.size),("compiler_extra_names",toJson (extraNames.map Name.toString)),
    ("modules",toJson moduleRows),("declarations",toJson declarations),
    ("mouths",toJson mouths),("body_edges",toJson cfg.bodyEdges),("type_edges",toJson cfg.typeEdges),
    ("paid_selected",toJson paidSelected),("paid_CIs",toJson paidCIs),("old_source_replays",toJson (0 : Nat)),
    ("source_target_reads",toJson (#[] : Array String)),("subject_free_base_imports",toJson (1 : Nat)),
    ("candidate_environment_imports",toJson (0 : Nat)),("base_modules",toJson base.header.modules.size)]
 IO.FS.writeFile cfg.output (report.pretty ++ "\n")
 emit s!"CP806_PASS logical={raw.size} kernel={checked.checkedCalls} inherited={inherited.size} axiomClosure={closure}"
