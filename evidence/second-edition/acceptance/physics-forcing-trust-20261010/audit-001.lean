import H0mework.Papers.SecondEditionPhysicsRegisteredForcing
import Lean

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open Lean Elab Command
private def releaseName (value : String) : Name :=
  (value.splitOn ".").foldl Name.str .anonymous

private def completeRefs (info : ConstantInfo) : NameSet := Id.run do
  let mut refs := info.type.getUsedConstantsAsSet ++ info.getUsedConstantsAsSet
  if let some value := info.value? true then refs := refs ++ value.getUsedConstantsAsSet
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

run_cmd do
  let env ← getEnv
  let roots : List (String × String) := [("BellRegisteredDuhamel.difference_contraction", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.every_finite_suffix_upper", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.geometric_sum_upper", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.geometric_telescopes", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.source_recycle_split", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.suffix_geometric", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.term", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.term_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.term_successor", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredDuhamel.transfer_complement", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredDuhamelTail"),
    ("BellRegisteredTensorAction.complete_adjoint_pair", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredTensorAction"),
    ("BellRegisteredTensorAction.opposite_side_recycle", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredTensorAction"),
    ("BellRegisteredTensorAction.same_side_recycle", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredTensorAction"),
    ("BellRegisteredTensorAction.source_tensor_left_right", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.RegisteredTensorAction"),
    ("BellSharedCEMBackground.BirthSource", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.first_birth_residual", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.first_residual_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.jointFactor", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.joint_birth_residual", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.joint_factor_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.joint_residual_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.localFactor", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.local_factor_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.q00", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.q01", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.q10", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.q11", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.rectangular_bernstein", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.rectangular_factor_lower", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.reported_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.reported_total", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.second_birth_residual", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.second_residual_nonnegative", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.source_first_factor_mean", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.source_first_factor_supermean", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.source_joint_factor_mean", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.source_joint_factor_supermean", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.source_second_factor_mean", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground"),
    ("BellSharedCEMBackground.source_second_factor_supermean", "H0mework.Versions.R71e.ReleaseMaterials.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.SharedCEMBackground")]
  for (decl, owner) in roots do
    let name := releaseName decl
    unless (env.checked.get.find? name).isSome do throwError "MISSING_DECLARATION {name}"
    let some index := env.getModuleIdxFor? name | throwError "MISSING_DECLARATION_MODULE {name}"
    unless env.header.moduleNames[index]! == releaseName owner do
      throwError "WRONG_DECLARATION_MODULE {name} expected={owner} actual={env.header.moduleNames[index]!}"
  let closure := recoveryClosure env (roots.map fun item => releaseName item.1)
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "UNCHECKED_CONSTANT {name}"
    if info.isUnsafe || info.isPartial then throwError "UNSAFE_PARTIAL {name}"
    edges := edges + (completeRefs info).size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "UNAPPROVED_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "MISSING_CONSTANT_VALUE {name}"
    | _ => pure ()
  let report := Json.mkObj [
    ("token", toJson "7326c6e37382b27519f5a0ccb23c8fd0b694c4c24f89df412c34a0fac096535a"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
