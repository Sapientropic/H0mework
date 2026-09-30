import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.Formation
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.CompleteRealization
import Lean

open Lean Elab Command
open SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
open FixedMotherRealization
set_option maxRecDepth 200000
set_option maxHeartbeats 0
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

private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => (completeRefs info).toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)

private partial def recoveryReach (edges : NameMap NameSet) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryReach edges rest seen
      else recoveryReach edges (((edges.find? name).getD {}).toArray.toList ++ rest)
        (seen.insert name)

private def recoveryArity : Expr → Nat
  | .forallE _ _ body _ => 1 + recoveryArity body
  | _ => 0

private def recoveryResultType : Expr → Expr
  | .forallE _ _ body _ => recoveryResultType body
  | type => type





private def moduleNames (env : Environment) (modules : Array Name) : Except String NameSet := do
  let mut names : NameSet := {}
  for module in modules do
    let some index := env.getModuleIdx? module | throw s!"MISSING_MODULE {module}"
    let data := env.header.moduleData[index.toNat]!
    for name in data.constNames do
      unless (env.checked.get.find? name).isSome do throw s!"UNCHECKED_OWN_DECLARATION {name}"
      names := names.insert name
    for name in data.extraConstNames do
      if (env.checked.get.find? name).isSome then names := names.insert name
  return names



private def specializationParts? (name : Name) : Option (Name × Name) :=
  visit name .anonymous
where
  visit (parent suffix : Name) : Option (Name × Name) :=
    match parent with
    | .str origin "_at_" => some (origin, suffix)
    | .anonymous => none
    | .str prior text => visit prior ((Name.str .anonymous text).appendCore suffix)
    | .num prior number => visit prior ((Name.num .anonymous number).appendCore suffix)
run_cmd do
  let env ← getEnv
  let modules := #[`SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.Formation, `SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.FixedMother.CompleteRealization]
  let own ← match moduleNames env modules with
    | .ok names => pure names
    | .error message => throwError message
  unless own.size == 64 do throwError "SIGNED_OWN_INVENTORY {own.size}"
  let closure := recoveryClosure env own.toArray.toList
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAUTHORIZED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_VALUE {name}"
    | _ => pure ()
  let mouth := ``root_admission_fixed_mother_complete_realization
  let some info := env.checked.get.find? mouth | throwError "MISSING_MOUTH"
  unless recoveryArity info.type == 0 do throwError "PUBLIC_PREMISE"
  let roots := recoveryClosure env [mouth]
  for required in [``low_formation, ``high_formation, ``MotherAdmittedWorld.every_state,
      ``MotherCompleteInquiry.every_source, ``MotherMacroSource.every_source,
      ``MotherFamilyOccurrence.MotherRoot, ``MotherFamilyOccurrence.MotherVisit,
      ``MotherPointwiseLaws.finiteLaw, ``MotherAdmittedWorld.formState,
      ``MotherMacroSource.Origin.form, ``MotherMaterialJoin.Mixed.combine] do
    unless roots.contains required do throwError "PROVENANCE_MISSING {required}"
  for module in env.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then
      throwError "UNEXPECTED_SCRATCH {module}"
  for name in [``lowProgramme_read, ``highProgramme_read, ``low_formation, ``high_formation, mouth] do
    let some info := env.checked.get.find? name | throwError "MOUTH_MISSING {name}"
    let used ← collectAxioms name
    logInfo m!"MOUTH {name} arity={recoveryArity info.type} levels={info.levelParams} type={info.type} axioms={used}"
  let registered := (Meta.instanceExtension.getState env).instanceNames
  let instances := own.toArray.filter registered.contains
  let mut codegen : Nat := 0
  for module in modules do
    let some index := env.getModuleIdx? module | throwError "MISSING_MODULE"
    let data := env.header.moduleData[index.toNat]!
    for name in data.extraConstNames do
      if !(env.checked.get.find? name).isSome then
        unless data.constNames.any (fun base => base.isPrefixOf name) do throwError "CODEGEN_ORIGIN {name}"
        unless !closure.contains name do throwError "TRUSTED_CODEGEN {name}"
        codegen := codegen + 1
  logInfo m!"FIXED_MOTHER_TRUST own={own.size} closure={closure.size} edges={edges} axioms={axioms.toArray} unsafe=0 partial=0 instances={instances.size} codegen_only={codegen} mouth_arity=0 full_metadata=1"
