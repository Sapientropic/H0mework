import H0mework.Papers.LowEnergyQ3MaterialsT
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
  let roots : List (String × String) := [("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.denominator", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.denominatorRay", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.denominator_factor", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.leading", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.numerator", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.numeratorRay", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.numerator_factor", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.rayResponse", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.ray_denominator_nonzero", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.ray_value", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.response", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.response_on_ray", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.source_ray_limit", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.Metric.two_directional_limits_differ", "H0mework.Physics.LowEnergy.BosonEffective.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.auxiliaryFirst", "H0mework.Physics.LowEnergy.BosonEffective.Order"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.auxiliaryFirst_inverse", "H0mework.Physics.LowEnergy.BosonEffective.Order"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.eliminated_row", "H0mework.Physics.LowEnergy.BosonEffective.Schur"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.eliminated_unique", "H0mework.Physics.LowEnergy.BosonEffective.Schur"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.elimination_order", "H0mework.Physics.LowEnergy.BosonEffective.Order"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.full_response", "H0mework.Physics.LowEnergy.BosonEffective.Schur"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.inverseJet", "H0mework.Physics.LowEnergy.BosonEffective.Taylor"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.inverseJet_exact", "H0mework.Physics.LowEnergy.BosonEffective.Taylor"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.inverseJet_residual", "H0mework.Physics.LowEnergy.BosonEffective.Taylor"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.inverse_remainder_bound", "H0mework.Physics.LowEnergy.BosonEffective.Analytic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.matterFirst", "H0mework.Physics.LowEnergy.BosonEffective.Order"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.matterWrite", "H0mework.Physics.LowEnergy.BosonEffective.Schur"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.original_source_remainder", "H0mework.Physics.LowEnergy.BosonEffective.Readback"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.original_source_response", "H0mework.Physics.LowEnergy.BosonEffective.Readback"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.perturbation_regular", "H0mework.Physics.LowEnergy.BosonEffective.Analytic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.retained_row", "H0mework.Physics.LowEnergy.BosonEffective.Schur"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.same_boson_kernel", "H0mework.Physics.LowEnergy.BosonEffective.Order"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective.schur", "H0mework.Physics.LowEnergy.BosonEffective.Schur"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.axialKernel", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.axialMix", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.blockPencil", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.characteristic", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.core", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.core_determinant", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.core_scale", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.first", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.first_characteristic_nonzero", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.inverseResidual", "H0mework.Physics.LowEnergy.LightKernel.Jet"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.kernel_is_zeroGraph", "H0mework.Physics.LowEnergy.LightKernel.Graph"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.metricContact", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.metricLeading", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.metricReader", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.metricSolution", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.metricSource", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.metric_divisor_physical", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.mixing", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.mixing_scale", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.original_metric_response", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pair", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pairDiagonal₁", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pairDiagonal₂", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pairSecond", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pairSecond_scale", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pair_determinant", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pair_scale", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.pencil", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadraticInverse", "H0mework.Physics.LowEnergy.LightKernel.Jet"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadraticReduced", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_determinant_factor", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_factor", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_frequency_pair", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_initial_determinant", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_inverse_exact", "H0mework.Physics.LowEnergy.LightKernel.Jet"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_inverse_residual", "H0mework.Physics.LowEnergy.LightKernel.Jet"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.quadratic_pair_generated", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.rayReduced", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.rayRowScale", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.ray_determinant_factor", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.ray_factor", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.ray_initial_determinant", "H0mework.Physics.LowEnergy.LightKernel.Scaling"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.realKernel", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.realMix", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.second", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.sourceOrder", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_axial_visible", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_block", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_complement_inverse", "H0mework.Physics.LowEnergy.LightKernel.Jet"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_first_kernel", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_metric_orthogonal", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_metric_solution", "H0mework.Physics.LowEnergy.LightKernel.Metric"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_quadratic_leading", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.source_ray_leading", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.staticCoreInverse", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.static_core_inverse", "H0mework.Physics.LowEnergy.LightKernel.Characteristic"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.vectorKernel", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.vectorMix", "H0mework.Physics.LowEnergy.LightKernel.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.zeroGraph", "H0mework.Physics.LowEnergy.LightKernel.Graph"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.zeroGraph_injective", "H0mework.Physics.LowEnergy.LightKernel.Graph"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.zeroGraph_kernel", "H0mework.Physics.LowEnergy.LightKernel.Graph"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.LightKernel.zeroGraph_retained", "H0mework.Physics.LowEnergy.LightKernel.Graph")]
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
    ("token", toJson "8c73a14db3edc90391ffc16de8f275e7ece9e02ccc0c0b7fba538c49bce6cac9"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
