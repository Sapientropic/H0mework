import H0mework.Physics.FullOccurrence.FixedAssemblySeamClosure
import H0mework.Physics.ElectricEC.FixedLorentzCriticalPair

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalLorentzClosure

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalGravityCurvatureSeam
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECLorentzCriticalPair
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeLorentzGeometricKinematics
open StageNineFormNativeMatterSpinThreeForm
open StageNineHolonomicField

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev GlobalActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev CartanActual : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart Source Current

private theorem global_coframe_eq_cartan :
    GlobalActual.coframe = CartanActual.coframe := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Current).coframe =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Current).coframe
  rw [sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_coframe,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_coframe]

private theorem global_connection_eq_cartan :
    GlobalActual.gravityConnection = CartanActual.gravityConnection := by
  exact
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityConnection_eq_cartan
      Source Current

private theorem global_auxiliary_eq_cartan :
    GlobalActual.gravityAuxiliary = CartanActual.gravityAuxiliary := by
  funext point
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Current).gravityAuxiliary point =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Current).gravityAuxiliary point
  rw [sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_gravityAuxiliary]
  exact
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary
      Source Current point).symm

private theorem global_matter_eq_cartan :
    GlobalActual.matter = CartanActual.matter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Current).matter =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Current).matter
  rw [sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_matter]

private theorem global_conjugateMatter_eq_cartan :
    GlobalActual.conjugateMatter = CartanActual.conjugateMatter := by
  change
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source Current).conjugateMatter =
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
        Source Current).conjugateMatter
  rw [sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_conjugateMatter]

private theorem global_matterSpin_eq_cartan
    (point : BasePoint) :
    formNativeMatterSpinThreeForm Source 0 point
        (toContinuumPointField GlobalActual point) =
      formNativeMatterSpinThreeForm Source 0 point
        (toContinuumPointField CartanActual point) := by
  have physicalSpinEquality :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      Source GlobalActual CartanActual point
      (congrFun global_coframe_eq_cartan point)
      (congrFun global_matter_eq_cartan point)
      (congrFun global_conjugateMatter_eq_cartan point)
  unfold diracDualFormNativeActionSpinResponseAt
    formNativePhysicalSpinCurrentThreeForm at physicalSpinEquality
  exact neg_injective physicalSpinEquality

private theorem global_auxiliaryExteriorCovariantDerivative_eq_cartan
    (point : BasePoint) :
    holonomicGravityAuxiliaryExteriorCovariantDerivative GlobalActual point =
      holonomicGravityAuxiliaryExteriorCovariantDerivative CartanActual point := by
  unfold holonomicGravityAuxiliaryExteriorCovariantDerivative
    holonomicGravityAuxiliaryJet gravityAuxiliaryDirectionalDerivative
  rw [global_connection_eq_cartan, global_auxiliary_eq_cartan]

theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_lorentzRead_eq_cartan
    (point : BasePoint) :
    holonomicFormNativeLorentzEulerThreeForm Source 0 GlobalActual point =
      holonomicFormNativeLorentzEulerThreeForm Source 0 CartanActual point := by
  unfold holonomicFormNativeLorentzEulerThreeForm
  rw [global_auxiliaryExteriorCovariantDerivative_eq_cartan,
    global_matterSpin_eq_cartan]

private theorem current_coframe_contDiff : ContDiff ℝ ∞ Current.coframe := by
  rw [fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_contDiff
      internal coordinate

private theorem current_coframe_nondegenerate
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    Matrix.det (Current.coframe (canonicalCauchySlicePoint time space)) ≠ 0 := by
  rw [fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_coframe_eq_preEC,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_coframe_nondegenerate
      space inDomain

/-- The source/current-only full-occurrence global producer restores the
Cartan-native Lorentz zero fiber on its one generated actual. -/
theorem
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_lorentz_zero_onDomain
    (time : ℝ)
    (space : StageNineSpatialPoint)
    (inDomain :
      time ∈ fixedP506L0FinalCommonTimeAxisOriginDomain space) :
    (diracDualFormNativePointwiseJointResidual Source GlobalActual
        (canonicalCauchySlicePoint time space)).lorentzConnection =
      0 := by
  change
    holonomicFormNativeLorentzEulerThreeForm Source 0 GlobalActual
        (canonicalCauchySlicePoint time space) =
      0
  rw [
    fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobal_lorentzRead_eq_cartan]
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      Source Current current_coframe_contDiff
      (canonicalCauchySlicePoint time space)
      (current_coframe_nondegenerate time space inDomain)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalLorentzClosure
