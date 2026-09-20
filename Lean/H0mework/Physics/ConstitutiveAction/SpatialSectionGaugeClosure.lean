import H0mework.Physics.ConstitutiveAction.SpatialSectionOperator

/-!
# Gauge-auxiliary closure of the constitutive spatial section

The spatial-section producer is defined before any residual is evaluated.
This module verifies its first full-domain action channel.  Canonical spatial
translation is shown to preserve the literal holonomic P286 curvature, so
the auxiliary installed independently at every contact is exactly the
constitutive inverse of the one global assembled connection.

No residual coordinate, sign, support branch, target field, or equation
certificate is accepted by the producer or by the translation seam.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance spatialSectionGaugeP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

private theorem canonicalSpatialContactTranslation_hasFDerivAt
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    HasFDerivAt (canonicalSpatialContactTranslation space)
      (ContinuousLinearMap.id ℝ BasePoint) point := by
  unfold canonicalSpatialContactTranslation
  fun_prop

/-- The raw P286 first jet of a spatially recentered current is the first jet
of the original current at the translated point. -/
theorem p286ConnectionDerivative_spatiallyRecenter
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (space : StageNineSpatialPoint)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286ConnectionDerivative
        (spatiallyRecenterHolonomicConfiguration current space)
        point derivativeDirection formDirection =
      p286ConnectionDerivative current
        (canonicalSpatialContactTranslation space point)
        derivativeDirection formDirection := by
  rcases smooth with
    ⟨_coframeSmooth, _gravityConnectionSmooth, _gravityAuxiliarySmooth,
      _multiplierSmooth, gaugeConnectionSmooth, _gaugeAuxiliarySmooth,
      _scalarSmooth, _matterSmooth, _conjugateMatterSmooth⟩
  let coordinateField : BasePoint → P286CoordinateCarrier :=
    fun candidate =>
      p286CoordinateEquiv (current.gaugeConnection candidate formDirection)
  have fieldDifferentiable :
      DifferentiableAt ℝ coordinateField
        (canonicalSpatialContactTranslation space point) :=
    ((gaugeConnectionSmooth formDirection).differentiable (by simp)
      ).differentiableAt
  have composed :=
    fieldDifferentiable.hasFDerivAt.comp point
      (canonicalSpatialContactTranslation_hasFDerivAt space point)
  unfold p286ConnectionDerivative fieldDirectionalDerivative
  change
    p286CoordinateEquiv.symm
        (fderiv ℝ
          (coordinateField ∘ canonicalSpatialContactTranslation space) point
          (coordinateDirection derivativeDirection)) =
      p286CoordinateEquiv.symm
        (fderiv ℝ coordinateField
          (canonicalSpatialContactTranslation space point)
          (coordinateDirection derivativeDirection))
  rw [composed.fderiv]
  simp

/-- Literal `dA + [A,A]` is faithful under canonical spatial recentering. -/
theorem holonomicGaugeCurvature_spatiallyRecenter
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (spatiallyRecenterHolonomicConfiguration current space) point =
      holonomicGaugeCurvature current
        (canonicalSpatialContactTranslation space point) := by
  funext pair
  unfold holonomicGaugeCurvature
  rw [p286ConnectionDerivative_spatiallyRecenter current smooth,
    p286ConnectionDerivative_spatiallyRecenter current smooth]
  rfl

/-- Global action normal form of the section auxiliary.  Although generated
contactwise, it is exactly the constitutive inverse of the original current's
literal coframe and curvature at the same global point. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint) :
    (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current).gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (current.coframe point)
        (holonomicGaugeCurvature current point) := by
  rw [← canonicalCauchySlicePoint_projections point,
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary_slice_actionWrite]
  unfold diracDualFormNativeConstitutiveAuxiliaryField
  rw [holonomicGaugeCurvature_spatiallyRecenter current smooth,
    canonicalSpatialContactTranslation_timeAxis]
  simp [spatiallyRecenterHolonomicConfiguration]

/-- The section output has the same literal P286 curvature as its input,
because the section producer preserves the full P286 connection field. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_curvature
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGaugeCurvature
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
          source current) point =
      holonomicGaugeCurvature current point := by
  exact
    holonomicGaugeCurvature_eq_of_connection_eq_current
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
        source current)
      current
      (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeConnection
        source current)
      point

/-- First full-domain zero-fiber channel of the new section actual.  The
equation is checked only after the action-owned section has been generated. -/
theorem
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliaryEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (point : BasePoint)
    (nondegenerate : Matrix.det (current.coframe point) ≠ 0) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField
        (diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
          source current) point) := by
  let output :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator
      source current
  have outputCoframe :
      output.coframe = current.coframe :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_coframe
      source current
  have outputCurvature :
      holonomicGaugeCurvature output point =
        holonomicGaugeCurvature current point :=
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_curvature
      source current point
  apply
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings source)
      (toContinuumPointField output point)
      (by
        change Matrix.det (output.coframe point) ≠ 0
        rw [outputCoframe]
        exact nondegenerate)).2
  change
    output.gaugeAuxiliary point =
      formNativeP286GaugeEliminatedAuxiliaryAtBoundary
        (sourceGeneratedUnifiedCouplings source)
        (output.coframe point)
        (holonomicGaugeCurvature output point)
  rw [outputCoframe, outputCurvature]
  exact
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliary
      source current smooth point

/-! ## Fixed P506/L0 checkpoint -/

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliaryEquation
    (space : StageNineSpatialPoint) :
    FormNativeP286GaugeAuxiliaryEquationAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space)) := by
  apply
    diracDualFormNativeConstitutiveJointActionSpatialSectionOperator_gaugeAuxiliaryEquation
  · exact fixedP506FormNativeJointActionSolvedSuccessor_smooth
  · rw [
      fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice]
    norm_num

theorem
    fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliaryResidual_zero
    (space : StageNineSpatialPoint) :
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
          (canonicalCauchySlicePoint 0 space)) =
      0 := by
  exact
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor
        (canonicalCauchySlicePoint 0 space))).2
      (fixedP506FormNativeConstitutiveJointActionSpatialSectionSuccessor_gaugeAuxiliaryEquation
        space)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionGaugeClosure
