import H0mework.Physics.JointVariation.LiveElectricGlobalDevelopmentOperator

/-!
# Fixed P506/L0 live-electric field transport

The live-electric global writer changes the temporal P286 auxiliary while
preserving the preceding global development's primitive matter, scalar,
coframe, and connection fields.  This module transports the derived Cartan,
curvature, covariant-derivative, and origin point-field reads across those
literal equalities.

These are transporter theorems only.  They do not generate either actual,
accept a residual, or turn a read into a write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- Stable API alias for the fixed source/current live-electric actual. -/
abbrev LiveActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual

/-- Stable API alias for its preceding complete-joint global development. -/
abbrev ExistingActual : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointGlobalDevelopmentActual

private abbrev LiveCartanInput : StageNineHolonomicConfiguration :=
  completeJointLiveElectricGlobalP286Current positiveSmoothUnifiedSource
    FixedInput

private abbrev ExistingCartanInput : StageNineHolonomicConfiguration :=
  completeJointGlobalP286Current positiveSmoothUnifiedSource FixedInput

private theorem actionCartanConnectionAt_eq_of_fields_at
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEqual : first.coframe = second.coframe)
    (matterEqual : first.matter point = second.matter point)
    (conjugateEqual :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionCartanConnectionAt
        positiveSmoothUnifiedSource first point =
      diracDualFormNativeActionCartanConnectionAt
        positiveSmoothUnifiedSource second point := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      positiveSmoothUnifiedSource first second point
      (congrFun coframeEqual point) matterEqual conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [coframeEqual, spinEqual]

/-- The live-electric P286 write does not alter the fields read by the Cartan
producer, so the final primitive Lorentz connection is literally the
preceding global connection. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityConnection_eq_existing :
    LiveActual.gravityConnection = ExistingActual.gravityConnection := by
  change
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource LiveCartanInput).gravityConnection =
    (sourceActionGeneratedDiracDualCartanReactionCurrentRestart
      positiveSmoothUnifiedSource ExistingCartanInput).gravityConnection
  rw [sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection]
  funext point
  apply actionCartanConnectionAt_eq_of_fields_at
  · exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing
      point
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing
      point

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalarCovariantDerivative_eq_existing :
    holonomicScalarCovariantDerivative LiveActual =
      holonomicScalarCovariantDerivative ExistingActual := by
  funext point direction
  unfold holonomicScalarCovariantDerivative
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing]

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing :
    holonomicGravityCurvature LiveActual =
      holonomicGravityCurvature ExistingActual := by
  funext point internalPair spacetimePair
  unfold holonomicGravityCurvature gravityConnectionDerivative
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityConnection_eq_existing]

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_contravariantGravityCurvature_eq_existing :
    holonomicContravariantGravityCurvature LiveActual =
      holonomicContravariantGravityCurvature ExistingActual := by
  funext point
  unfold holonomicContravariantGravityCurvature
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing]

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityAuxiliary_eq_existing :
    LiveActual.gravityAuxiliary = ExistingActual.gravityAuxiliary := by
  funext point
  calc
    LiveActual.gravityAuxiliary point =
        physicalIIPlusBivector (LiveActual.coframe point) :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary
        positiveSmoothUnifiedSource LiveCartanInput point
    _ = physicalIIPlusBivector (ExistingActual.coframe point) := by
      rw [
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing]
    _ = ExistingActual.gravityAuxiliary point :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliary
        positiveSmoothUnifiedSource ExistingCartanInput point).symm

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravitySimplicityMultiplier_eq_existing :
    LiveActual.gravitySimplicityMultiplier =
      ExistingActual.gravitySimplicityMultiplier := by
  calc
    LiveActual.gravitySimplicityMultiplier =
        formNativeGravityReactionField LiveActual :=
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        positiveSmoothUnifiedSource LiveCartanInput
    _ = formNativeGravityReactionField ExistingActual := by
      funext point
      unfold formNativeGravityReactionField
      rw [
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityAuxiliary_eq_existing,
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_contravariantGravityCurvature_eq_existing]
    _ = ExistingActual.gravitySimplicityMultiplier :=
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_reaction_selfGenerated
        positiveSmoothUnifiedSource ExistingCartanInput).symm

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeCurvature_eq_existing :
    holonomicGaugeCurvature LiveActual =
      holonomicGaugeCurvature ExistingActual := by
  funext point pair
  unfold holonomicGaugeCurvature p286ConnectionDerivative
    fieldDirectionalDerivative
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing]

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matterCovariantDerivative_eq_existing :
    holonomicMatterCovariantDerivative LiveActual =
      holonomicMatterCovariantDerivative ExistingActual := by
  funext point direction
  unfold holonomicMatterCovariantDerivative
  rw [
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityConnection_eq_existing,
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing]

/-- At the common origin the live auxiliary also agrees, so every component
of the generated continuum point field is identical to the preceding global
development. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_pointField_origin_eq_existing :
    toContinuumPointField LiveActual 0 =
      toContinuumPointField ExistingActual 0 := by
  apply StageNineContinuumPointField.ext <;>
    simp only [toContinuumPointField]
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityCurvature_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravityAuxiliary_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gravitySimplicityMultiplier_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeCurvature_eq_existing
      0
  · exact
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeAuxiliary_origin_eq_existing
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalarCovariantDerivative_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matterCovariantDerivative_eq_existing
      0
  · exact congrFun
      fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing
      0

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricFieldTransport
