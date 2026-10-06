import H0mework.Papers.PhysicsCommonSourceHRelease
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
  let roots : List (String × String) := [("SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion.pairing_secondQuantize_oneParticle", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckFermion"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.Fermion.secondQuantize_oneParticle", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckFermion"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.complex_current_preserved", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.currentEvaluation", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.currentEvaluation_eq", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.currentPreparation", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.currentPreparation_eq", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.fockCurrentResponse", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.fockEvaluation", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.fockEvaluation_eq_source", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.full_dual_response_preserved", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.full_p286_current_preserved", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.initial_agreement_dark_separation", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckControls"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.nextEvaluation", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.nextEvaluation_eq", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.nextPreparation", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.nextPreparation_eq", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.physical_current_preserved", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.physical_stress_preserved", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.preparedFock", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.preparedFock_normalized", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.sameOccurrence_current_prediction", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.sameOccurrence_quantization_check", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckConsumer"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.sourceIndexOrder", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.QuantizationCheck.source_generator_prediction", "H0mework.Physics.ConstitutiveInterfacesQuantization.CheckCurrent"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.StageEightGravityGaugeMatterCredential", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.StageEightGravityGaugeMatterCredential.generatedLineage_height_pos", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.StageEightGravityGaugeMatterCredential.selectedEndpoint", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.StageEightGravityGaugeMatterCredential.selectedEndpoint_eq_eleven", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.canonicalSource_generates_correctedStageEightGravityGaugeMatterCredential", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.canonicalStageEightGravityGaugeMatterCredential", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.legacyFixedProbeMatterConfiguration", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.legacyFixedProbeMatterConfiguration_ne_generated", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.legacyFixedProbeMatterConfiguration_rejected", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.mismatchedMatterConfiguration_rejected", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.stageEightCredentialGeometry", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.stageEightCredentialGeometry_eq_source", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.stageEightJointMatterConfiguration", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential.zeroPhaseSource_rejects_stageEightGravityGaugeMatterCredential", "H0mework.Physics.Matter.SU7GravityGaugeMatterJointCredential"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.DeterministicPreparationPrediction", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.SameOccurrenceBellPrediction", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.colorXFrame", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.color_x_action", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.deterministicPreparationPrediction", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.nextProbability", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.next_probability", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.phiVector", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.phiVector_normalized", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.phi_from_fixed_family", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.phi_from_original_runtime", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.phi_joint_probability", "H0mework.Physics.Bell.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.rawPreparedVector", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.runtimeProbability", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.runtime_probability", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.Bell.sameOccurrenceBellPrediction", "H0mework.Physics.Bell.Runtime"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.amplitude_bound", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.energy_balance", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.field_changes", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.helicity_changes", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.initialQ_derivative", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.initialQ_nonzero", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.CompleteOrbit.momentum_bound", "H0mework.Physics.GlobalOrbit.Observable"),
    ("SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Global.sourceGlobalDynamicsClosure", "H0mework.Physics.GlobalOrbit.Acceptance"),
    ("SaturationMonoid.PhysicsCore.Stage10.GroundedRealization.source_realization_consumed", "H0mework.Physics.MotherSource.GroundedRealization"),
    ("SaturationMonoid.PhysicsCore.Stage10.GroundedRealization.whole_matter_action", "H0mework.Physics.MotherSource.GroundedRealization"),
    ("SaturationMonoid.PhysicsCore.Stage10.Prediction.sourceClosedJoint", "H0mework.Physics.RootRuntime.PredictionDimensionlessJoint"),
    ("SaturationMonoid.PhysicsCore.Stage10.RawSourceRealization.original_consumer", "H0mework.Physics.MotherSource.RawSourceRealization"),
    ("SaturationMonoid.PhysicsCore.Stage10.RawSourceRealization.represented_history", "H0mework.Physics.MotherSource.RawSourceRealization"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.StageOneThroughTenClosure", "H0mework.Physics.RootRuntime.RecoveryConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.currentMatter", "H0mework.Physics.RootRuntime.RecoveryMatter"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.source_restriction", "H0mework.Physics.RootRuntime.RecoverySource"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.stageEight", "H0mework.Physics.RootRuntime.RecoverySource"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.stageEight_generated", "H0mework.Physics.RootRuntime.RecoverySource"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.stageOneThroughTenClosed", "H0mework.Physics.RootRuntime.RecoveryConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.stageOneThroughTenClosure", "H0mework.Physics.RootRuntime.RecoveryConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.stageSix", "H0mework.Physics.RootRuntime.RecoverySource"),
    ("SaturationMonoid.PhysicsCore.Stage10.Recovery.stageSix_generated", "H0mework.Physics.RootRuntime.RecoverySource"),
    ("SaturationMonoid.PhysicsCore.Stage10.Runtime.allMacroNext", "H0mework.Physics.RootRuntime.RuntimeActivation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Runtime.nextConfiguration", "H0mework.Physics.RootRuntime.RuntimeConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.Runtime.sameOccurrenceActivation", "H0mework.Physics.RootRuntime.RuntimeActivation"),
    ("SaturationMonoid.PhysicsCore.Stage10.Runtime.stageTenClosed", "H0mework.Physics.RootRuntime.RuntimeConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.material_acceptance_iff", "H0mework.Physics.SourceFormation.Acceptance"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.material_original", "H0mework.Physics.SourceFormation.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ArbitrarySourceFormation.material_realization", "H0mework.Physics.SourceFormation.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes.every_programme_consumed", "H0mework.Physics.MotherProgrammesFormationProgrammes.AutonomousConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.AutonomousProgrammes.source_birth_consumed", "H0mework.Physics.MotherProgrammesFormationProgrammes.AutonomousConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF.action_elimination", "H0mework.Physics.MotherProgrammesFormationClockBF.Action"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF.action_normalForm", "H0mework.Physics.MotherProgrammesFormationClockBF.Action"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF.generatedB_unique", "H0mework.Physics.MotherProgrammesFormationClockBF.Calculus"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBF.quadraticBlock_value", "H0mework.Physics.MotherProgrammesFormationClockBF.Calculus"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFFeedback.source_feedback_consumed", "H0mework.Physics.MotherProgrammesFormationClockBF.Feedback"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFPreparation.constitutive_update", "H0mework.Physics.MotherProgrammesFormationClockBF.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFPreparation.native_consumed", "H0mework.Physics.MotherProgrammesFormationClockBF.Preparation"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliary.action_decomposition", "H0mework.Physics.SourceFormation.AuxiliaryAction"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliary.configuration_decomposition", "H0mework.Physics.SourceFormation.AuxiliaryAction"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryConsumer.source_family_consumed", "H0mework.Physics.MotherProgrammesFormation.FullAuxiliaryConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryFields.action_in_generated_fields", "H0mework.Physics.SourceFormation.AuxiliaryFields"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.FullAuxiliaryFields.wholeEquiv", "H0mework.Physics.SourceFormation.AuxiliaryFields"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution.occupied_normalized", "H0mework.Physics.SourceFormation.EvolutionConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution.quantum_response", "H0mework.Physics.SourceFormation.EvolutionConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution.whole_native_consumed", "H0mework.Physics.SourceFormation.EvolutionConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin.all_source_evolution_is_native", "H0mework.Physics.MotherDeclarationsAll.SourceOriginConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin.all_source_native_compiled", "H0mework.Physics.MotherDeclarationsAll.SourceOriginConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin.all_source_writer_consumed", "H0mework.Physics.MotherDeclarationsAll.SourceOriginConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier.source_feedback_formed", "H0mework.Physics.MotherDeclarationsJoint.CarrierFormationConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier.whole_carrier_formed", "H0mework.Physics.MotherDeclarationsJoint.CarrierFormationCoverage"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions.every_operator", "H0mework.Physics.MotherProgrammesFormationMatter.ActionMatrix"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions.finite_matrix", "H0mework.Physics.MotherProgrammesFormationMatter.ActionMatrix"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions.finite_native_consumed", "H0mework.Physics.MotherProgrammesFormationMatter.ActionConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions.native_consumed", "H0mework.Physics.MotherProgrammesFormationMatter.ActionConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMatterActions.operatorEquiv", "H0mework.Physics.MotherProgrammesFormationMatter.ActionMatrix"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPointwiseLaws.every_law", "H0mework.Physics.MotherLaws.PointwiseCompletion"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProcessLaws.regular_process_map", "H0mework.Physics.MotherLaws.RestrictionProcess"),
    ("SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.RawSourcePaths.ordered_physical_sources", "H0mework.Physics.MotherProgrammesFormationPaths.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage10.WholeDescription.source_description_closed", "H0mework.Physics.MotherDescription.Consumer"),
    ("SaturationMonoid.PhysicsCore.Stage9CU.Fields.history_compact_jet_bound", "H0mework.Physics.Actual.FieldsHistoryBounds"),
    ("SaturationMonoid.PhysicsCore.Stage9CU.Weak.actuals_compact_jet_bound", "H0mework.Physics.Actual.WeakCompactBounds"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.actual_action_quantumResponse", "H0mework.Physics.QuantumCompatibility.DualResponse"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.actual_covariantAction", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.covariantAction", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.exteriorTransport_remainder", "H0mework.Physics.QuantumCompatibility.ExteriorRemainder"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.frozenMatterDensity", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.frozenMatterDensity_eq_classical", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.frozenMatterDensity_hasDerivAt", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.kineticAction", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.kineticLoad", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.kineticLoad_eq_actual", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.kineticLoad_source_prediction", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.kineticObservable", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.physicalCompatibility", "H0mework.Physics.QuantumCompatibility.Acceptance"),
    ("SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility.temporalAction", "H0mework.Physics.QuantumCompatibility.Stress"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.ActualFoundation", "H0mework.Physics.QuantumFoundation.FoundationAcceptance"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualAction", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualAction_holonomic", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualAuxiliary_generated", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualChartField", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualChartField_matter", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualChartField_vacuum", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualConstitutive_solves", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualDensity_descent", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualFoundation", "H0mework.Physics.QuantumFoundation.FoundationAcceptance"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualGlobalMatter", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualGlobalMatter_in_chart", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualGlobalMatter_section", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualGravityIIPlus", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualHodge", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalMatter", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalMatter_overlap", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalMatter_zero", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalPotential", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalPotential_adjoint", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalPotential_overlap", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalPotential_zero", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualLocalSpin_invariant", "H0mework.Physics.QuantumFoundation.FoundationInvariance"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualPotential_adjoint", "H0mework.Physics.QuantumFoundation.FoundationDescent"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualResidual_sameAction", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualVacuum_stabilizer", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.actualVacuum_uniqueMinimum", "H0mework.Physics.QuantumFoundation.FoundationNativeAction"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.nativeActionInFrame", "H0mework.Physics.QuantumFoundation.FoundationInvariance"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.nativeActionInFrame_actual", "H0mework.Physics.QuantumFoundation.FoundationInvariance"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Foundation.nativeActionInFrame_change", "H0mework.Physics.QuantumFoundation.FoundationInvariance"),
    ("SaturationMonoid.PhysicsCore.Stage9G.Runtime.stageNineClosed", "H0mework.Physics.QuantumFoundation.RuntimeConsumer"),
    ("SaturationMonoid.PhysicsCore.Stage9G.SourceGeneratedContinuousQuantumUnifiedTheoryCredential", "H0mework.Physics.QuantumFoundation.Credential"),
    ("SaturationMonoid.PhysicsCore.Stage9G.sourceGeneratedContinuousQuantumUnifiedTheory", "H0mework.Physics.QuantumFoundation.Credential"),
    ("SaturationMonoid.PhysicsCore.Stage9G.sourceGeneratedContinuousQuantumUnifiedTheoryCredential", "H0mework.Physics.QuantumFoundation.Credential"),
    ("SaturationMonoid.PhysicsCore.Stage9G.sourceGeneratedUniqueClassicalActual", "H0mework.Physics.QuantumFoundation.Classical"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.ClassicalWorldAcceptance", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.ClassicalWorldAcceptance.gravityBianchi", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.ClassicalWorldAcceptance.p286GaugeBianchi", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.ClassicalWorldAcceptance.pointwiseJointZeroFiber", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.DynamicScalarSourceContactAtOrigin", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.coframeSectorBalance", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.gravityBianchi", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.integrableJointShellZeroFiber", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.integratedSourceRelativeP286Ward", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.jointShellZeroFiber", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.lorentzSectorBalance", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.p286GaugeBianchi", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.p286SectorBalance", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyClassicalWorldAcceptance.strongEquation", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyIntegratedSourceRelativeP286Ward", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacySimultaneousSixSectorNonzero", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacySimultaneousSixSectorNonzero.toPhysicalSectors", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.LegacyStageNineCClassicalWorldFamily", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.MatterCurrentNonzeroAt", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.MatterSpinNonzeroAt", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.SimultaneousSixPhysicalSectorNonzero", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.SpinTorsionCompatible", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.StressOrSpinNonzeroAt", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineCClassicalWorldAcceptance.smooth_nondegenerate_integrable_implies_legacyIntegratedSourceRelativeP286Ward", "H0mework.Physics.Geometry.CClassicalAcceptance"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.SourceGeneratedStageNineAGlobalGeometryCredential", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.UnifiedMotherAxisParallelODE", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.embeddedP286HyperchargeElement_commutes_generatedUnifiedMotherPotential", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.embeddedP286HyperchargeElement_commutes_p286LieBlockEmbed", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedLocalUnifiedMotherPotential", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedLocalUnifiedMotherPotential_overlap_gauge", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedLocalUnifiedMotherPotential_overlap_linear", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedMotherAxisGenerator", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedMotherAxisGenerator_eq_pathContraction", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedMotherAxisGenerator_negativeUnit", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedMotherAxisPath", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedTransition_adjoint_hyperchargeShift", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedTransition_adjoint_localUnifiedMotherPotential", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedTransition_adjoint_unifiedMotherPotential", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherAxisTransport", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherAxisTransport_add", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherAxisTransport_hasDerivAt", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherAxisTransport_recovers_stageEightFirstJet", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherAxisTransport_solves_parallelODE", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherAxisTransport_zero", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.generatedUnifiedMotherPotential_axisPath", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.positiveSourceGeneratedStageNineAGlobalGeometryCredential", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.positive_generatedMotherAxisGenerator_zero_nonzero", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.positive_generatedMotherAxisGenerators_do_not_commute", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.positive_generatedTransitionLogDerivative_zero_one_nonzero", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.positive_generatedUnifiedMotherAxisTransport_nonconstant", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.stageEightExteriorDerivativeComponent_self", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.StageNineFullMotherDescentAndTransport.unshiftedUnifiedMotherPotential_badGluing_rejected", "H0mework.Physics.Geometry.FullMotherDescentAndTransport"),
    ("SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet.feature_derivative", "H0mework.Physics.YangMillsSourceQuantum.TimeJet"),
    ("SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet.jetEnergy_physical", "H0mework.Physics.YangMillsSourceQuantum.JetEnergy"),
    ("SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet.momentumRead_eq", "H0mework.Physics.YangMillsSourceQuantum.TimeJet"),
    ("SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet.quantum_jet_physical_energy", "H0mework.Physics.YangMillsSourceQuantum.JetEnergy"),
    ("SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet.radiusRead_eq", "H0mework.Physics.YangMillsSourceQuantum.TimeJet"),
    ("SaturationMonoid.PhysicsCore.YangMills.NativeSource.TimeJet.rateRead_eq", "H0mework.Physics.YangMillsSourceQuantum.TimeJet")]
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
    ("token", toJson "774b29a7515684a939e386c4b522bc3428bb9995f49975abb4afe9fcda44ed78"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
