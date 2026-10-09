import H0mework.Papers.PhysicsCommonSourceCapRelease
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
  let roots : List (String × String) := [("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualA_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisField_coupled_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisField_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisField_whole", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualAxisWindow_tendsto", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointGenerator_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointGenerator_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointKernel_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointKernel_original", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointResolvent_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointTime_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_actualJointTime_source_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_rawForm_momentum_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_rawReader_momentum_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentTensor_actual", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentTensor_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_actual", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_tensor", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_returnedCurrentWindow_zero", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_sourceFiniteSet_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_sourcePhysicalSpan_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationFullPoleContinuationAudit.checked_sourceRetainer_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationFullPoleContinuation"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceActualN1_gaussColorCore", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColorCharge_hermitian", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColorCharge_pair", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColorCovariantTorque_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeAction", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeAdjoint", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeDerivative", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeMixed", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeMomentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_coframeTerm", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_covariant_connection", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_directional", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_number", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_scalar", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_spinCurrent", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceColor_spin_full", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceConfigurationTorque_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceConfigurationTorque_ward", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceMatterTorque_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceNativeActionWard", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceNativeOperator_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalGaussColorTorqueAudit.checked_sourceNativeSandwichWard", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalGaussColorTorque"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceActualMode_contact_deviation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceContactKernel_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceEmittedContact_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeContactSymbol_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeForm_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeReader_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceNativeSample_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPhysicalModeContactAudit.checked_sourceReferenceContact_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPhysicalModeContact"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualAxisField_compatibility", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualAxisField_constraint_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualAxisField_native_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualOriginWeight_cosource114", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualOriginWeight_native", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualOriginWeight_native_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualResidue_native_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_actualResidue_sourcePoleVector", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_axisCosource_actual", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_axisCosource_tendsto", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_axisNullCosource_tendsto", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_configurationDeviationWindow_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_originCosource114_actualWard", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_origin_native_Ward_balance", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_sourceDeviationKernel_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationPoleConstraintReturnAudit.checked_sourceDeviationRead_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationPoleConstraintReturn"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualC_affine", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualC_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualC_difference_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeTensor_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeTensor_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeTensor_same_carrier", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_actualModeWindow_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_coordinates", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_creation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_fiber", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_left_unitary", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_preparation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_prepared", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_primal", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_restCoefficient", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_right_unitary", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_values", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_movingOverlap_zero", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceModeKernel_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceResolvent_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceResolvent_difference_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceTensor_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceTensor_same_carrier", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationSharedPoleCarrierAudit.checked_sourceTime_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.AuditCanonicalPreparationSharedPoleCarrier"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualA_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_coupled_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisField_whole", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualAxisWindow_tendsto", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualCurrentTensor", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointGenerator_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointKernel_original", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.actualJointTime_source_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.rawForm_momentum_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReaderMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.rawReader_momentum_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReaderMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_actual", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentTensor_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_actual", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_tensor", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.returnedCurrentWindow_zero", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFullPoleTensor"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.sourceFiniteSet_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.sourcePhysicalSpan_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.sourceReaderMomentumForm", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReaderMomentum"),
    ("LowEnergy.PreparationVacuumFullPoleContinuation.sourceRetainer_momentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRetainerMomentum"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.QuantumEnd", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceActualN1_gaussColorCore", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorChargeFiber", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_hermitian", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCharge_pair", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorConnectionFiber", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorCovariantTorque_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColorWardOperator", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAction", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeAdjoint", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeDerivative", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMixed", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeMomentum", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_coframeTerm", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_covariant_connection", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_directional", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussConnection"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_number", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_scalar", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spinCurrent", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceColor_spin_full", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceConfigurationTorque_ward", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorqueFiber", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceMatterTorque_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussColorWard"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeActionWard", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeOperator_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichTorque", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeSandwichWard", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalGaussColorTorque.sourceNativeTorque", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaussKineticTorque"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceActualMode_contact_deviation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceContactKernel_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationForm", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationKernel", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationReader", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceDeviationSample", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceEmittedContact_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeDeviationSymbol", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeNativeSymbol"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceModeField", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeNativeSymbol"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeContactSymbol_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeNativeSymbol"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeForm_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeReader_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceNativeSample_mode", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceModeContactRead"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceContact_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact"),
    ("LowEnergy.PreparationVacuumPhysicalModeContact.sourceReferenceState", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceReferenceContact"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_compatibility", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_constraint_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualAxisField_native_residue", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_cosource114", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualOriginWeight_native_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_native_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.actualResidue_sourcePoleVector", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_actual", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.axisCosource_tendsto", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.axisNullCosource_tendsto", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceAxisCompatibility"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationPrice", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.configurationDeviationWindow_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.nativeContactWindow", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.originCosource114_actualWard", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.originWardBoundary", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.origin_native_Ward_balance", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePoleBalance"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationKernel_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.sourceDeviationRead_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumPoleConstraintReturn.sourcePoleVector", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNativePolePrice"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_affine", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualC_difference_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeTensor_same_carrier", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.actualModeWindow_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_coordinates", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_creation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_fiber", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_left_unitary", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_preparation", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_prepared", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_primal", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_restCoefficient", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_right_unitary", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_values", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMovingCarrier"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.movingOverlap_zero", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceModeKernel_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceMomentumLinear", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceResolvent_difference_price", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_generated", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTensor_same_carrier", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedTensor"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceTime_continuous", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocity", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation"),
    ("LowEnergy.PreparationVacuumSharedPoleCarrier.sourceVelocityLinear", "H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentumContinuation")]
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
    ("token", toJson "dd88b36ef18cc432239986bf65a1af062dc72a4caadac98a027e40310b78be85"), ("roots", toJson roots.length),
    ("constants", toJson closure.size), ("edges", toJson edges),
    ("axioms", toJson (axioms.toArray.toList.map Name.toString)),
    ("unsafe", toJson (0 : Nat)), ("partial", toJson (0 : Nat)),
    ("full_metadata", toJson true)]
  logInfo m!"FIRST_RELEASE_TRUST {report.compress}"
