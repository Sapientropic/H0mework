import H0mework.Papers.PhysicsCommonSourceAbRelease
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
  let roots : List (String × String) := [("LowEnergy.PreparationVacuumActionDecomposition.physical_action_decomposition", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationActionCoreDecomposition"),
    ("LowEnergy.PreparationVacuumElectricConstraint.charge_pair", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.embed_dense", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.jointCoreGraph", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.jointReader", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.jointReader_adjoint_core", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.jointReader_core", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.jointReader_price", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.orbitAdjoint", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.orbit_adjoint_pair", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.orbit_pair", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.original_joint_graph_closed", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.original_weighted_ordering", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.sourceApprox_joint_graph", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumElectricConstraint.weighted_adjoint_constraint", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricWeightedGraph"),
    ("LowEnergy.PreparationVacuumEngineCancellation.sourceEngineForces_successor_zero", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineCancellationForces"),
    ("LowEnergy.PreparationVacuumEngineSource.sourceEngine_generated", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineProgram"),
    ("LowEnergy.PreparationVacuumFullElectricWard.compressionDefect", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.compressionDefect_eventually", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.curvatureChannels_same_state", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPreparedWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.finite_full_core", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.finite_full_core_eventually", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.full_current", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.original_action_components", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.original_full_ward", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairCurrent", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairCurrent_apply", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairCurrent_oneParticle", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairCurrent_original_words", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairFiber", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairFiber_coordinates", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairFiber_sub", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.pairFiber_weight", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.physical_full_ward", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.preparedChannels_same_state", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPreparedWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.quantized_normal_order", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent"),
    ("LowEnergy.PreparationVacuumFullElectricWard.resolvedChannels_original_response", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPreparedWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.wardCore", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.wardDefect", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.yukawaCutDefect", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullElectricWard.yukawaTorque", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricCoreWard"),
    ("LowEnergy.PreparationVacuumFullEnergyForm.actual_closed_form_complete_energy", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFullEnergyForm"),
    ("LowEnergy.PreparationVacuumHalfDensityFiber.diagonalFiber_source", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationHalfDensityCompressionFeed"),
    ("LowEnergy.PreparationVacuumSourcePreparedResponse.preparedLaplace_derivative", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNonlinearState"),
    ("LowEnergy.PreparationVacuumSourcePreparedResponse.preparedLaplace_remainder", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNonlinearState"),
    ("LowEnergy.PreparationVacuumSourcePreparedResponse.sourceCausalState_same_preparation", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCausalState"),
    ("LowEnergy.PreparationVacuumSourcePreparedResponse.sourceNonlinearState_same_preparation", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNonlinearState"),
    ("LowEnergy.PreparationVacuumSourcePreparedState.preparationSequence_residual", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceBoundarySequence"),
    ("LowEnergy.PreparationVacuumSourcePreparedState.preparationSequence_yukawa_residual", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceBoundarySequence"),
    ("LowEnergy.PreparationVacuumSourcePreparedState.sourcePreparation_exists", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedState"),
    ("LowEnergy.PreparationVacuumSourcePreparedState.sourceRemainder_decomposition", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRemainder"),
    ("LowEnergy.PreparationVacuumSourcePreparedState.sourceRemainder_readback", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRemainder"),
    ("LowEnergy.PreparationVacuumSourcePreparedState.sourceRemainder_selfAdjoint", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRemainder"),
    ("LowEnergy.PreparationVacuumTemporalCharge.chargePrice", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.chargePrice_nonnegative", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.globalReader", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.globalReader_norm", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.globalReader_source", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporalCoefficient", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_affine", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_contact_balance", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_contact_core", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_contact_fiber", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_core", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_full_family", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_full_matrix", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_hamiltonian", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_hamiltonian_first", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_hamiltonian_valid", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumTemporalCharge.temporal_state_fiber", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalGlobalCharge"),
    ("LowEnergy.PreparationVacuumUncutYukawa.curvature_first_exchange", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaObservedLimit"),
    ("LowEnergy.PreparationVacuumUncutYukawa.curvature_second_exchange", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaObservedLimit"),
    ("LowEnergy.PreparationVacuumUncutYukawa.observed_first_exchange", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaObservedLimit"),
    ("LowEnergy.PreparationVacuumUncutYukawa.observed_second_exchange", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaObservedLimit"),
    ("LowEnergy.PreparationVacuumUncutYukawa.observed_uncut_limit_near", "H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationYukawaObservedLimit"),
    ("LowEnergy.SourceBoundedInsertionTime.actual_uniform_time_response", "H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceBoundedInsertionTime"),
    ("LowEnergy.SourceHamiltonianSpectralMeasure.actual_source_spectral_measure", "H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceHamiltonianSpectralMeasure")]
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
    ("token", toJson "17c898f4e77f9922343c93a0413168a614b6356465b7270b675a2fab553eb009"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
