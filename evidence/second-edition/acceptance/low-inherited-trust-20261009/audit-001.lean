import H0mework.Papers.LowEnergyPhenomenology
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
  let roots : List (String × String) := [("SaturationMonoid.PhysicsCore.LowEnergy.Consumer.source_fixed_inventory_diagnostic", "H0mework.Physics.LowEnergy.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Consumer.source_inventory_beta", "H0mework.Physics.LowEnergy.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Consumer.source_mass_entry", "H0mework.Physics.LowEnergy.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Solution.joint_zero", "H0mework.Physics.LowEnergyEvolution.Full"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.UniformDevelopment.joint_zero", "H0mework.Physics.LowEnergyEvolution.Uniform"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.UniformDevelopment.norm_control", "H0mework.Physics.LowEnergyEvolution.Uniform"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation.initial_derivative", "H0mework.Physics.LowEnergyEvolution.VariationDerivative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation.initial_fderiv", "H0mework.Physics.LowEnergyEvolution.VariationDerivative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation.initial_variation_evolves", "H0mework.Physics.LowEnergyEvolution.VariationDerivative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Evolution.uniformDevelopment_exists", "H0mework.Physics.LowEnergyEvolution.Uniform"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Exchange.original_current", "H0mework.Physics.LowEnergyExchange.Current"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Exchange.original_current_exchange", "H0mework.Physics.LowEnergyExchange.Static"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Fermion.actual_color_fourFermion", "H0mework.Physics.LowEnergyFermion.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Fermion.actual_color_fourFermion_normalized", "H0mework.Physics.LowEnergyFermion.Consumer"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullPhase.canonical_preserved", "H0mework.Physics.LowEnergyFullPhase.Preparation"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullPhase.gamma_preserved", "H0mework.Physics.LowEnergyFullPhase.Operator"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullPhase.kinetic_phase_term", "H0mework.Physics.LowEnergyFullPhase.Derivative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullPhase.prepared_pair_preserved", "H0mework.Physics.LowEnergyFullPhase.Preparation"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.FullPhase.yukawa_preserved", "H0mework.Physics.LowEnergyFullPhase.Operator"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.JointMass.coefficient_actual", "H0mework.Physics.LowEnergy.JointMassCoordinates"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.JointMass.outputGram_actual", "H0mework.Physics.LowEnergy.JointMassCoordinates"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Kinetic.four_leg_amplitude_normalized", "H0mework.Physics.LowEnergyKinetic.Scale"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Kinetic.normalized_right_unit", "H0mework.Physics.LowEnergyKinetic.Scale"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Kinetic.original_action_time_affine", "H0mework.Physics.LowEnergyKinetic.Density"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalLocal.original_current_derivative", "H0mework.Physics.LowEnergyMatterSpace.GlobalOriginal"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalLocal.original_field_derivative", "H0mework.Physics.LowEnergyMatterSpace.GlobalOriginal"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalLocal.original_prepared_source_derivative", "H0mework.Physics.LowEnergyMatterSpace.GlobalOriginal"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalPerturbedDevelopment.current_kubo", "H0mework.Physics.LowEnergyMatterSpace.GlobalResponse"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalPerturbedDevelopment.current_source", "H0mework.Physics.LowEnergyMatterSpace.GlobalResponse"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalPerturbedDevelopment.operator_derivative", "H0mework.Physics.LowEnergyMatterSpace.GlobalResponse"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.GlobalPerturbedDevelopment.unitary", "H0mework.Physics.LowEnergyMatterSpace.GlobalFlow"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.PerturbedDevelopment.couplingOperator_derivative", "H0mework.Physics.LowEnergyMatterSpace.PerturbedOperator"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.currentVariation_kubo", "H0mework.Physics.LowEnergyMatterSpace.SpatialResponseKubo"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.globalPerturbedDevelopment", "H0mework.Physics.LowEnergyMatterSpace.GlobalFlow"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.local_native_kubo", "H0mework.Physics.LowEnergyMatterSpace.SpatialResponseSource"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.local_source_CAR", "H0mework.Physics.LowEnergyMatterSpace.SpatialResponseSource"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.perturbed_global_exists", "H0mework.Physics.LowEnergyMatterSpace.GlobalGlue"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response.perturbed_quadratic_remainder", "H0mework.Physics.LowEnergyMatterSpace.PerturbedVariation"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.ResponsePhase.originalKernel_prepared_readback", "H0mework.Physics.LowEnergyMatterSpace.SpatialResponsePhaseKubo"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR.source_native_allWord", "H0mework.Physics.LowEnergyMatterSpace.SpatialCARNative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR.spatialMoment_positive", "H0mework.Physics.LowEnergyMatterSpace.SpatialCARState"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR.wordObservable_response", "H0mework.Physics.LowEnergyMatterSpace.SpatialCARNative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.SpatialCAR.wordOperator", "H0mework.Physics.LowEnergyMatterSpace.SpatialCARWords"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.duhamel_dual_weak", "H0mework.Physics.LowEnergyMatterSpace.DualWeak"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.gaugeCurrentMatrix_weight", "H0mework.Physics.LowEnergyMatterSpace.CurrentOperator"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.gauge_history_prepares_nonempty", "H0mework.Physics.LowEnergyMatterSpace.PreparationGauge"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.normalizedPreparationNative_sourceResponse", "H0mework.Physics.LowEnergyMatterSpace.PreparationNative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.original_primal_hamiltonian", "H0mework.Physics.LowEnergyMatterSpace.PrimalSymbol"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.preparationMap_norm", "H0mework.Physics.LowEnergyMatterSpace.PreparationHistory"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.preparationNative_original_dual", "H0mework.Physics.LowEnergyMatterSpace.PreparationNative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.preparationNative_sourceResponse", "H0mework.Physics.LowEnergyMatterSpace.PreparationNative"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.schwartz_hamiltonian_value", "H0mework.Physics.LowEnergyMatterSpace.GeneratorSchwartz"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.sourceHamiltonian_hermitian", "H0mework.Physics.LowEnergyMatterSpace.Source"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.source_domain_iff", "H0mework.Physics.LowEnergyMatterSpace.GeneratorDomain"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.source_hamiltonian_value", "H0mework.Physics.LowEnergyMatterSpace.GeneratorDomain"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.spatialUnitary_add", "H0mework.Physics.LowEnergyMatterSpace.Spatial"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Normalization.native_boundary", "H0mework.Physics.LowEnergy.Normalization"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Quantum.compression_product", "H0mework.Physics.LowEnergyQuantum.Compression"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Quantum.moving_composite_response", "H0mework.Physics.LowEnergyQuantum.Readout"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Quantum.moving_response", "H0mework.Physics.LowEnergyQuantum.Readout"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Quantum.source_joint_and_response", "H0mework.Physics.LowEnergyQuantum.Readout"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Quantum.spatial_volume_response", "H0mework.Physics.LowEnergyQuantum.Density"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Running.normal_forms", "H0mework.Physics.LowEnergy.Running"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.ScalarInventory.b0_table", "H0mework.Physics.LowEnergy.ScalarInventory"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Spacetime.fundamentalTime_equation", "H0mework.Physics.LowEnergySpacetime.Propagation"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Spacetime.fundamentalWave_actual_nonzero_speed", "H0mework.Physics.LowEnergySpacetime.Cauchy"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Spacetime.fundamentalWave_nine_channels", "H0mework.Physics.LowEnergySpacetime.Cauchy"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Spacetime.fundamentalWave_operator", "H0mework.Physics.LowEnergySpacetime.Propagation"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Spacetime.fundamentalWave_residual", "H0mework.Physics.LowEnergySpacetime.Cauchy"),
    ("SaturationMonoid.PhysicsCore.LowEnergy.Spacetime.radial_residual", "H0mework.Physics.LowEnergySpacetime.Jacobi")]
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
    ("token", toJson "c2c20fc80e41c3244947ed730bb5382467b6d841e665ea238613719c02be516f"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
