import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.Formation
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.CompleteRealization
import Lean

open Lean Elab Command
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def moduleRelocations : NameMap Name :=
  ((({} : NameMap Name).insert `scratch.MotherSourceTheorem.Formation `SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.Formation).insert `scratch.MotherSourceTheorem.CompleteRealization `SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.CompleteRealization)
private def privateRelocations : NameMap Name :=
  ((({} : NameMap Name).insert `_private.scratch.MotherSourceTheorem.Formation `_private.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.Formation).insert `_private.scratch.MotherSourceTheorem.CompleteRealization `_private.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.CompleteRealization)
private def binderModulePrefix (name : Name) : Option Name :=
  visit name .anonymous
where
  visit (parent suffix : Name) : Option Name :=
    match parent with
    | .str _ "_@" | .str _ "_private" | .num (.str _ "_hygCtx") _ | .num (.str (.str _ "_@") "_internal") _ =>
        (moduleRelocations.find? suffix).map (fun mapped => parent.appendCore mapped)
    | .anonymous => none
    | .str prior text => visit prior ((Name.str .anonymous text).appendCore suffix)
    | .num prior number => visit prior ((Name.num .anonymous number).appendCore suffix)
private partial def productionName (name : Name) : Name :=
  if let some renamed := moduleRelocations.find? name then renamed
  else if let some renamed := privateRelocations.find? name then renamed
  else if let some renamed := binderModulePrefix name then productionName renamed
  else match name with
    | .anonymous => .anonymous
    | .str parent text => .str (productionName parent) text
    | .num parent number => .num (productionName parent) number
private def relocatedModule (name : Name) : Name := (moduleRelocations.find? name).getD name
private def sourceEdits : Option Name → List (Nat × Nat × Nat)
  | some `scratch.MotherSourceTheorem.Formation => []
  | some `scratch.MotherSourceTheorem.CompleteRealization => [(7, 44, 109)]
  | _ => []
private def sourcePositionMatches (edits : List (Nat × Nat × Nat)) (before after : Nat) : Bool :=
  check edits 0
where
  check : List (Nat × Nat × Nat) → Int → Bool
    | [], delta => (before : Int) + delta == (after : Int)
    | (first, last, size) :: rest, delta =>
        if before ≤ first then (before : Int) + delta == (after : Int)
        else if before < last then false
        else check rest (delta + (size : Int) - ((last - first : Nat) : Int))

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.getUsedConstantsAsSet
  match info with
  | .defnInfo val => for name in val.all do refs := refs.insert name
  | .thmInfo val => for name in val.all do refs := refs.insert name
  | .opaqueInfo val => for name in val.all do refs := refs.insert name
  | .inductInfo val =>
      for name in val.all ++ val.ctors do refs := refs.insert name
  | .ctorInfo val => refs := refs.insert val.induct
  | .recInfo val =>
      for name in val.all do refs := refs.insert name
      for rule in val.rules do
        refs := refs.insert rule.ctor
        refs := refs ++ rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return refs

private partial def promotionClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then promotionClosure env rest seen
    else
      let children := match env.checked.get.find? name with
        | some info => (completeRefs info).toArray.toList
        | none => []
      promotionClosure env (children ++ rest) (seen.insert name)




-- Position correspondence follows the exact source rewrite, with no namespace changes.
private def relocatedSourceInfo (edits : List (Nat × Nat × Nat)) : SourceInfo → SourceInfo → Bool
  | .none, .none => true
  | .original leading first trailing last, .original leading' first' trailing' last' =>
      leading.toString == leading'.toString && trailing.toString == trailing'.toString &&
      sourcePositionMatches edits first.byteIdx first'.byteIdx && sourcePositionMatches edits last.byteIdx last'.byteIdx
  | .synthetic first last canonical, .synthetic first' last' canonical' =>
      canonical == canonical' &&
      ((first.byteIdx == first'.byteIdx && last.byteIdx == last'.byteIdx) ||
        (sourcePositionMatches edits first.byteIdx first'.byteIdx && sourcePositionMatches edits last.byteIdx last'.byteIdx))
  | _, _ => false

private def relocatedPreresolved : Syntax.Preresolved → Syntax.Preresolved → Bool
  | .namespace first, .namespace last => productionName first == last
  | .decl first fields, .decl last fields' => productionName first == last && fields == fields'
  | _, _ => false

private partial def relocatedSyntax (edits : List (Nat × Nat × Nat)) : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node info kind args, .node info' kind' args' =>
      relocatedSourceInfo edits info info' && productionName kind == kind' && args.size == args'.size &&
        (args.zip args').all (fun (first, last) => relocatedSyntax edits first last)
  | .atom info text, .atom info' text' => relocatedSourceInfo edits info info' && text == text'
  | .ident info raw name resolved, .ident info' raw' name' resolved' =>
      relocatedSourceInfo edits info info' && raw.toString == raw'.toString &&
        productionName name == name' && resolved.length == resolved'.length &&
        (resolved.zip resolved').all (fun (first, last) => relocatedPreresolved first last)
  | _, _ => false

private def relocatedMetadata (edits : List (Nat × Nat × Nat)) (first last : MData) : Bool :=
  first.entries.length == last.entries.length &&
    (first.entries.zip last.entries).all (fun ((key, value), (key', value')) =>
      key == key' &&
        if key == `_recAppPos then
          match value, value' with
          | .ofNat before, .ofNat after => sourcePositionMatches edits before after
          | _, _ => false
        else if key == `_recApp then
          match value, value' with
          | .ofSyntax before, .ofSyntax after => relocatedSyntax edits before after
          | _, _ => false
        else match value, value' with
          | .ofSyntax before, .ofSyntax after => before.eqWithInfo after
          | _, _ => value == value')

-- Pointer keys distinguish expressions whose built-in equality forgets syntax source info.
-- This helper runs only in the audit command, never in a mathematical declaration.
private partial def quotedName? (expr : Expr) : Option Name := do
  let fn ← expr.getAppFn.constName?
  let args := expr.getAppArgs
  if fn == ``Name.anonymous && args.isEmpty then return .anonymous
  if (fn == ``Name.mkStr || fn == ``Name.str) && args.size == 2 then
    let parent ← quotedName? args[0]!
    let .lit (.strVal text) := args[1]! | none
    return .str parent text
  if (fn == ``Name.mkNum || fn == ``Name.num) && args.size == 2 then
    let parent ← quotedName? args[0]!
    let number ← args[1]!.rawNatLit? <|>
      (if args[1]!.isAppOfArity ``OfNat.ofNat 3 then
        args[1]!.getAppArgs[1]!.rawNatLit? else none)
    return .num parent number
  for size in List.range 8 do
    if fn == .str ``Name ("mkStr" ++ toString (size + 1)) && args.size == size + 1 then
      return ← args.foldlM (init := Name.anonymous) fun parent arg => do
        let .lit (.strVal text) := arg | none
        return .str parent text
  none

private def relocatedLevel (rename : Name → Name) : Level → Level
  | .zero => .zero
  | .succ level => .succ (relocatedLevel rename level)
  | .max first last => .max (relocatedLevel rename first) (relocatedLevel rename last)
  | .imax first last => .imax (relocatedLevel rename first) (relocatedLevel rename last)
  | .param name => .param (rename name)
  | .mvar name => .mvar name

private def sameLevelParameters (rename : Name → Name) (first last : List Name) : Bool :=
  let mapped := first.map rename
  first.eraseDups.length == first.length && mapped.eraseDups.length == first.length && mapped == last

private unsafe def completeExprEqual (rename : Name → Name) (sameData : MData → MData → Bool)
    (exactBinders : Bool) (first last : Expr) : Bool :=
  let rec visit (first last : Expr) : StateM (Std.HashMap (Ptr Expr × Ptr Expr) Bool) Bool := do
    let key : Ptr Expr × Ptr Expr := (⟨first⟩, ⟨last⟩)
    if let some known := (← get)[key]? then return known
    let result ← if let some before := quotedName? first then
      match quotedName? last with
      | some after => pure (rename before == after)
      | none => pure false
    else match first, last with
      | .bvar a, .bvar b => pure (a == b)
      | .fvar a, .fvar b => pure (a == b)
      | .mvar a, .mvar b => pure (a == b)
      | .sort a, .sort b => pure (relocatedLevel rename a == b)
      | .const a us, .const b vs => pure (rename a == b && us.map (relocatedLevel rename) == vs)
      | .app f a, .app g b => do pure ((← visit f g) && (← visit a b))
      | .lam n t b i, .lam m u c j | .forallE n t b i, .forallE m u c j =>
          do pure ((!exactBinders || rename n == m) && i == j && (← visit t u) && (← visit b c))
      | .letE n t v b d, .letE m u w c e =>
          do pure ((!exactBinders || rename n == m) && d == e && (← visit t u) && (← visit v w) && (← visit b c))
      | .lit a, .lit b => pure (a == b)
      | .mdata a b, .mdata c d => do pure (sameData a c && (← visit b d))
      | .proj a i b, .proj c j d => do pure (rename a == c && i == j && (← visit b d))
      | _, _ => pure false
    modify (fun memo => memo.insert key result)
    return result
  (visit first last).run' {}

private unsafe def explainExpr (rename : Name → Name) (sameData : MData → MData → Bool)
    (first last : Expr) : String :=
  let rec visit (first last : Expr) : String :=
    if completeExprEqual rename sameData true first last then "same"
    else match first, last with
    | .const a us, .const b vs => s!"constant before={a} mapped={rename a} after={b} levels={repr us}/{repr vs}"
    | .app f a, .app g b =>
        if !completeExprEqual rename sameData true f g then "function/" ++ visit f g else "argument/" ++ visit a b
    | .lam n t b i, .lam m u d j | .forallE n t b i, .forallE m u d j =>
        if rename n != m then s!"binder before={repr n} mapped={repr (rename n)} after={repr m}"
        else if i != j then "binderInfo"
        else if !completeExprEqual rename sameData true t u then "domain/" ++ visit t u
        else "body/" ++ visit b d
    | .letE n t v b d, .letE m u w c e =>
        if rename n != m then s!"letBinder before={repr n} mapped={repr (rename n)} after={repr m}"
        else if d != e then "letNondep"
        else if !completeExprEqual rename sameData true t u then "letType/" ++ visit t u
        else if !completeExprEqual rename sameData true v w then "letValue/" ++ visit v w
        else "letBody/" ++ visit b c
    | .mdata a b, .mdata c d =>
        if !sameData a c then s!"metadata before={repr a} after={repr c}" else "annotated/" ++ visit b d
    | .proj a i b, .proj c j d =>
        if rename a != c || i != j then s!"projection {a}/{c} {i}/{j}" else "projected/" ++ visit b d
    | _, _ => s!"shape first={repr first} last={repr last}"
  visit first last

private def exactMetadata (first last : MData) : Bool :=
  first.entries.length == last.entries.length &&
    (first.entries.zip last.entries).all (fun ((key, value), (key', value')) =>
      key == key' && match value, value' with
        | .ofSyntax before, .ofSyntax after => before.eqWithInfo after
        | _, _ => value == value')

private def sameDeclarationMetadata (rename : Name → Name) (sameExpr : Expr → Expr → Bool)
    (first last : ConstantInfo) : Bool :=
  match first, last with
  | .axiomInfo a, .axiomInfo b => a.isUnsafe == b.isUnsafe
  | .defnInfo a, .defnInfo b =>
      a.hints == b.hints && a.safety == b.safety && a.all.map rename == b.all
  | .thmInfo a, .thmInfo b => a.all.map rename == b.all
  | .opaqueInfo a, .opaqueInfo b => a.isUnsafe == b.isUnsafe && a.all.map rename == b.all
  | .inductInfo a, .inductInfo b =>
      a.numParams == b.numParams && a.numIndices == b.numIndices &&
      a.all.map rename == b.all && a.ctors.map rename == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b =>
      rename a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams &&
      a.numFields == b.numFields && a.isUnsafe == b.isUnsafe
  | .recInfo a, .recInfo b =>
      a.all.map rename == b.all && a.numParams == b.numParams &&
      a.numIndices == b.numIndices && a.numMotives == b.numMotives &&
      a.numMinors == b.numMinors && a.k == b.k && a.isUnsafe == b.isUnsafe &&
      a.rules.length == b.rules.length &&
      (a.rules.zip b.rules).all (fun (r, s) =>
        rename r.ctor == s.ctor && r.nfields == s.nfields && sameExpr r.rhs s.rhs)
  | .quotInfo a, .quotInfo b =>
      match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | _, _ => false

private def relocatedInstanceKey : Meta.DiscrTree.Key → Meta.DiscrTree.Key
  | .const name arity => .const (productionName name) arity
  | .proj name index arity => .proj (productionName name) index arity
  | remaining => remaining
private def specializationParts? (name : Name) : Option (Name × Name) :=
  visit name .anonymous
where
  visit (parent suffix : Name) : Option (Name × Name) :=
    match parent with
    | .str origin "_at_" => some (origin, suffix)
    | .anonymous => none
    | .str prior text => visit prior ((Name.str .anonymous text).appendCore suffix)
    | .num prior number => visit prior ((Name.num .anonymous number).appendCore suffix)
private def moduleInventory (env : Environment) (modules : Array Name) : Except String (NameSet × NameSet) := do
  let mut own : NameSet := {}
  let mut codegen : NameSet := {}
  for module in modules do
    let some index := env.getModuleIdx? module | throw s!"MISSING_MODULE {module}"
    let data := env.header.moduleData[index.toNat]!
    for name in data.constNames do
      unless (env.checked.get.find? name).isSome do throw s!"UNCHECKED_OWN {name}"
      own := own.insert name
    for name in data.extraConstNames do
      if (env.checked.get.find? name).isSome then own := own.insert name
      else
        unless data.constNames.any (fun base => base.isPrefixOf name) do
          let some (original, context) := specializationParts? name | throw s!"CODEGEN_ORIGIN {name}"
          unless (env.checked.get.find? original).isSome || data.extraConstNames.contains original do
            throw s!"SPECIALIZATION_FUNCTION_ORIGIN {name}"
          unless data.constNames.any (fun base => base.isPrefixOf context) do
            throw s!"SPECIALIZATION_CONTEXT_ORIGIN {name}"
        codegen := codegen.insert name
  return (own, codegen)

run_cmd do
  let production ← getEnv
  Lean.enableInitializersExecution
  let candidate ← importModules #[{module := `scratch.MotherSourceTheorem.Formation}, {module := `scratch.MotherSourceTheorem.CompleteRealization}] {} 0 (loadExts := true)
  let candidateModules := #[`scratch.MotherSourceTheorem.Formation, `scratch.MotherSourceTheorem.CompleteRealization]
  let productionModules := #[`SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.Formation, `SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.CompleteRealization]
  let owner := fun (env : Environment) name =>
    (env.getModuleIdxFor? name).map (fun i => env.header.moduleNames[i.toNat]!)
  let (own, codegen) ← match moduleInventory candidate candidateModules with
    | .ok value => pure value
    | .error message => throwError message
  let (after, afterCodegen) ← match moduleInventory production productionModules with
    | .ok value => pure value
    | .error message => throwError message
  let mappedOwn := own.toArray.foldl (fun result name => result.insert (productionName name)) ({} : NameSet)
  unless own.size == 64 && mappedOwn.size == own.size && mappedOwn.size == after.size &&
      after.toArray.all mappedOwn.contains do throwError "OWN_INVENTORY_BIJECTION {own.size} {after.size}"
  unless codegen.isEmpty && afterCodegen.isEmpty do throwError "UNEXPECTED_CODEGEN"
  for module in production.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"
  let firstInstances := (Meta.instanceExtension.getState candidate).instanceNames
  let lastInstances := (Meta.instanceExtension.getState production).instanceNames
  for name in own.toArray do
    let moved := productionName name
    let some first := candidate.checked.get.find? name | throwError "OWN_MISSING {name}"
    let some last := production.checked.get.find? moved | throwError "PRODUCTION_MISSING {moved}"
    let sameExpr := completeExprEqual productionName (relocatedMetadata (sourceEdits (owner candidate name))) true
    unless (owner candidate name).map relocatedModule == owner production moved do throwError "OWN_OWNER {name}"
    unless sameLevelParameters productionName first.levelParams last.levelParams do throwError "OWN_LEVEL_PARAMETERS {name}"
    unless sameExpr first.type last.type do throwError "OWN_TYPE {name}: {explainExpr productionName (relocatedMetadata (sourceEdits (owner candidate name))) first.type last.type}"
    unless (match first.value? true, last.value? true with
      | some a, some b => sameExpr a b
      | none, none => true
      | _, _ => false) do throwError "OWN_VALUE {name}: {match first.value? true, last.value? true with | some a, some b => explainExpr productionName (relocatedMetadata (sourceEdits (owner candidate name))) a b | _, _ => "missing"}"
    unless sameDeclarationMetadata productionName sameExpr first last do throwError "OWN_METADATA {name}"
    unless firstInstances.contains name == lastInstances.contains moved do throwError "INSTANCE_CHANGED {name}"
  let full := promotionClosure candidate own.toArray.toList
  let productionFull := promotionClosure production after.toArray.toList
  let mappedFull := full.toArray.foldl (fun result name => result.insert (productionName name)) ({} : NameSet)
  unless mappedFull.size == full.size && full.size == productionFull.size &&
    productionFull.toArray.all mappedFull.contains do throwError "CLOSURE_BIJECTION"
  let mut edges := 0
  let mut shared : Nat := 0
  let mut sharedOwners : NameSet := {}
  let mut axioms : NameSet := {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in full.toArray do
    let moved := productionName name
    let some first := candidate.checked.get.find? name | throwError "UNCHECKED_CANDIDATE {name}"
    let some last := production.checked.get.find? moved | throwError "UNCHECKED_PRODUCTION {moved}"
    unless (owner candidate name).map relocatedModule == owner production moved do throwError "CLOSURE_OWNER {name}"
    if first.isUnsafe || first.isPartial || last.isUnsafe || last.isPartial then throwError "UNSAFE_PARTIAL {name}"
    let beforeRefs := completeRefs first
    let afterRefs := completeRefs last
    let mappedRefs := beforeRefs.toArray.foldl (fun result ref => result.insert (productionName ref)) ({} : NameSet)
    unless mappedRefs.size == beforeRefs.size && beforeRefs.size == afterRefs.size &&
      afterRefs.toArray.all mappedRefs.contains do throwError "CLOSURE_EDGE_BIJECTION {name}"
    edges := edges + beforeRefs.size
    if !own.contains name then
      unless moved == name && owner candidate name == owner production name do throwError "SHARED_MODULE_CHANGED {name}"
      shared := shared + 1
      if let some module := owner candidate name then sharedOwners := sharedOwners.insert module
    match first, last with
    | .axiomInfo _, .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAUTHORIZED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _, .defnInfo _ | .thmInfo _, .thmInfo _ | .opaqueInfo _, .opaqueInfo _ =>
        unless (first.value? true).isSome && (last.value? true).isSome do throwError "MISSING_VALUE {name}"
    | _, _ => pure ()
  let sampleName := `fixedMotherAuditUniverse
  let sampleLevel := Level.param sampleName
  let same := completeExprEqual productionName exactMetadata true
  unless same (.sort sampleLevel) (.sort sampleLevel) do throwError "LEVEL_POSITIVE_CONTROL"
  if same (.sort (.succ sampleLevel)) (.sort sampleLevel) ||
      same (.const ``Nat [.succ sampleLevel]) (.const ``Nat [sampleLevel]) then
    throwError "UNIVERSE_STRUCTURE_COLLAPSED"
  IO.FS.writeFile ".cache/fixed-mother-promotion/shared-owner-modules.json" (toJson (sharedOwners.toArray.map Name.toString)).pretty
  IO.FS.writeFile ".cache/fixed-mother-promotion/parity-own-names.json" (toJson (after.toArray.map Name.toString)).pretty
  logInfo m!"FIXED_MOTHER_PARITY own={own.size} complete_type_value_metadata=1 full_closure={full.size} full_edges={edges} shared_same_module_olean_nodes={shared} owner_edge_bijection=1 axioms={axioms.toArray} unsafe=0 partial=0 codegen=0 instance_delta=0 universe_structure_negative_controls=1"
