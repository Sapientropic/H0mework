import H0mework.Physics.Coframe.LinearPlebanskiCoframeActionPrincipal
import H0mework.Physics.MatterCurrent.EinsteinCartanPrimitiveCauchyUpdate

/-!
# S9-C3h151: action-generated P506 matter coframe stress

C3h149 generates the complete P506/L0 Einstein--Cartan primitive update and
replays its local actual `U₁` at the initial spacetime contact.  This module
reads the matter action of that already generated actual along the fixed
coframe shear

`e(t) = I + t E₃₀`.

The actual contorsion makes the third covariant derivative
`D₃ ψ = -(i / 8) ψ₂`.  The inverse tetrad then changes only the `γ³` kinetic
channel, so the complete densitized matter action is exactly affine:

`L_matter(e(t)) = L_matter(I) - t / 8`.

Consequently the actual matter stress covector has coordinate
`T(E₃₀) = -1/8` and is nonzero.  No stress, residual, endpoint, inverse
principal, range witness, coefficient, or branch receipt is accepted by a
constructor.  The shear is only a variation used after `U₁` has been
generated.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCoframeStress

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCoframeSectorStress
open StageNineCoframeVariation
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineJointActionLocalActualLift
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineMatterVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentCartanActual
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanPrimitiveCauchyUpdate
open StageNineSourceGeneratedMatterSpinActionUpdate
open SU7ExteriorBreakingYukawa
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## Fixed coframe action path -/

/-- The fixed off-diagonal coframe shear used to read the `E₃₀` action
coordinate.  It is a variation path, not source data. -/
def p506CoframeShear30 (parameter : ℝ) : LorentzianCoframe :=
  Matrix.transvection (3 : Fin 4) (0 : Fin 4) parameter

@[simp] theorem p506CoframeShear30_det (parameter : ℝ) :
    Matrix.det (p506CoframeShear30 parameter) = 1 := by
  change
    Matrix.det
        (Matrix.transvection (3 : Fin 4) (0 : Fin 4) parameter) =
      1
  have distinct : (3 : Fin 4) ≠ (0 : Fin 4) := by decide
  exact
    Matrix.det_transvection_of_ne (R := ℝ)
      (i := (3 : Fin 4)) (j := (0 : Fin 4)) distinct parameter

theorem p506CoframeShear30_inverse (parameter : ℝ) :
    (p506CoframeShear30 parameter)⁻¹ =
      p506CoframeShear30 (-parameter) := by
  apply Matrix.inv_eq_left_inv
  change
    Matrix.transvection (3 : Fin 4) (0 : Fin 4) (-parameter) *
        Matrix.transvection (3 : Fin 4) (0 : Fin 4) parameter =
      1
  have distinct : (3 : Fin 4) ≠ (0 : Fin 4) := by decide
  simpa using
    (Matrix.transvection_mul_transvection_same (R := ℝ)
      (i := (3 : Fin 4)) (j := (0 : Fin 4)) distinct
      (-parameter) parameter)

theorem p506CoframeShear30_eq_identity_add
    (parameter : ℝ) :
    p506CoframeShear30 parameter =
      (1 : LorentzianCoframe) +
        parameter • coframeCoordinateDirection 3 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [p506CoframeShear30, Matrix.transvection,
      coframeCoordinateDirection]

theorem inverseCoframeDiracGamma_p506CoframeShear30
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := p506CoframeShear30 parameter, derivative := 0 }
        direction =
      ![diracGamma 0, diracGamma 1, diracGamma 2,
        diracGamma 3 - (parameter : ℂ) • diracGamma 0] direction := by
  rw [inverseCoframeDiracGamma]
  change
    ∑ internalDirection : LorentzianIndex,
        (((p506CoframeShear30 parameter)⁻¹
          direction internalDirection : ℝ) : ℂ) •
          diracGamma internalDirection =
      _
  rw [p506CoframeShear30_inverse]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [p506CoframeShear30, Matrix.transvection, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring

theorem diracMatrixMatterAction_sub_smul_matrix
    (first second : DiracMatrix) (parameter : ℂ)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first - parameter • second) matter =
      diracMatrixMatterAction first matter -
        parameter • diracMatrixMatterAction second matter := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    diracMatrixMatterAction_add_matrix]
  rw [show -(parameter • second) = (-parameter) • second by
    simp]
  rw [diracMatrixMatterAction_smul_matrix]
  module

theorem p506_selectedMatterVector :
    Complex.I • diracMatrixMatterAction (diracGamma 0)
        ((-(Complex.I / 8)) • diracSpinTwoMatterProbe) =
      (1 / 8 : ℂ) • diracSpinZeroMatterProbe := by
  rw [map_smul]
  rw [show diracGamma (0 : LorentzianIndex) = diracGammaZero by
    rfl,
    diracGammaZero_maps_spinTwoProbe]
  rw [smul_smul]
  congr 1
  rw [show Complex.I / 8 = Complex.I * (8 : ℂ)⁻¹ by
    rw [div_eq_mul_inv]]
  rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
  ring

/-! ## Exact affine matter-action response -/

theorem generatedContinuumMatterVector_p506CoframeShear30
    (field : StageNineContinuumPointField)
    (derivativeThree :
      field.matterCovariantDerivative 3 =
        (-(Complex.I / 8)) • diracSpinTwoMatterProbe)
    (parameter : ℝ) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe field (p506CoframeShear30 parameter)) =
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe field 1) -
        (parameter / 8 : ℝ) • diracSpinZeroMatterProbe := by
  unfold generatedContinuumMatterVector
  simp only [withCoframe, scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart]
  simp_rw [inverseCoframeDiracGamma_p506CoframeShear30]
  simp_rw [show
      ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
        PointwiseLorentzianCoframeJet) =
      identityCoframeMatterGeometry by
    rfl]
  simp_rw [inverseCoframeDiracGamma_identity]
  simp only [Fin.sum_univ_four]
  change
    Complex.I •
          (diracMatrixMatterAction (diracGamma 0)
              (field.matterCovariantDerivative 0) +
            diracMatrixMatterAction (diracGamma 1)
              (field.matterCovariantDerivative 1) +
            diracMatrixMatterAction (diracGamma 2)
              (field.matterCovariantDerivative 2) +
            diracMatrixMatterAction
              (diracGamma 3 - (parameter : ℂ) • diracGamma 0)
              (field.matterCovariantDerivative 3)) +
        chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm field.scalar) field.matter =
      Complex.I •
          (diracMatrixMatterAction (diracGamma 0)
              (field.matterCovariantDerivative 0) +
            diracMatrixMatterAction (diracGamma 1)
              (field.matterCovariantDerivative 1) +
            diracMatrixMatterAction (diracGamma 2)
              (field.matterCovariantDerivative 2) +
            diracMatrixMatterAction (diracGamma 3)
              (field.matterCovariantDerivative 3)) +
        chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm field.scalar) field.matter -
        (parameter / 8 : ℝ) • diracSpinZeroMatterProbe
  rw [derivativeThree]
  rw [diracMatrixMatterAction_sub_smul_matrix]
  have selectedScaled :
      Complex.I •
          (diracMatrixMatterAction (diracGamma 3)
              ((-(Complex.I / 8)) • diracSpinTwoMatterProbe) -
            (parameter : ℂ) •
              diracMatrixMatterAction (diracGamma 0)
                ((-(Complex.I / 8)) • diracSpinTwoMatterProbe)) =
        Complex.I • diracMatrixMatterAction (diracGamma 3)
            ((-(Complex.I / 8)) • diracSpinTwoMatterProbe) -
          (parameter / 8 : ℝ) • diracSpinZeroMatterProbe := by
    rw [smul_sub]
    rw [show
      Complex.I • ((parameter : ℂ) •
          diracMatrixMatterAction (diracGamma 0)
            ((-(Complex.I / 8)) • diracSpinTwoMatterProbe)) =
        (parameter : ℂ) •
          (Complex.I • diracMatrixMatterAction (diracGamma 0)
            ((-(Complex.I / 8)) • diracSpinTwoMatterProbe)) by
      module]
    rw [p506_selectedMatterVector]
    module
  rw [show
    Complex.I •
        (diracMatrixMatterAction (diracGamma 0)
              (field.matterCovariantDerivative 0) +
          diracMatrixMatterAction (diracGamma 1)
              (field.matterCovariantDerivative 1) +
          diracMatrixMatterAction (diracGamma 2)
              (field.matterCovariantDerivative 2) +
          (diracMatrixMatterAction (diracGamma 3)
              ((-(Complex.I / 8)) • diracSpinTwoMatterProbe) -
            (parameter : ℂ) •
              diracMatrixMatterAction (diracGamma 0)
                ((-(Complex.I / 8)) • diracSpinTwoMatterProbe))) =
      Complex.I •
        (diracMatrixMatterAction (diracGamma 0)
              (field.matterCovariantDerivative 0) +
          diracMatrixMatterAction (diracGamma 1)
              (field.matterCovariantDerivative 1) +
          diracMatrixMatterAction (diracGamma 2)
              (field.matterCovariantDerivative 2)) +
      Complex.I •
        (diracMatrixMatterAction (diracGamma 3)
              ((-(Complex.I / 8)) • diracSpinTwoMatterProbe) -
          (parameter : ℂ) •
            diracMatrixMatterAction (diracGamma 0)
              ((-(Complex.I / 8)) • diracSpinTwoMatterProbe)) by
    module]
  rw [selectedScaled]
  module

theorem coframeMatterSectorLocalDensity_p506CoframeShear30
    (field : StageNineContinuumPointField)
    (conjugateMatter :
      field.conjugateMatter =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier))
    (derivativeThree :
      field.matterCovariantDerivative 3 =
        (-(Complex.I / 8)) • diracSpinTwoMatterProbe)
    (parameter : ℝ) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0 field
        (p506CoframeShear30 parameter) =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0 field 1 -
        parameter / 8 := by
  unfold coframeMatterSectorLocalDensity generatedVolumeDensity
  change
    |Matrix.det (p506CoframeShear30 parameter)| *
        generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
          (withCoframe field (p506CoframeShear30 parameter)) =
      |Matrix.det (1 : LorentzianCoframe)| *
          generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
            (withCoframe field 1) -
        parameter / 8
  rw [p506CoframeShear30_det]
  simp only [abs_one, one_mul, Matrix.det_one]
  unfold generatedContinuumMatterDensity
  simp only [matterDualFrameRelative_zeroChart]
  rw [generatedContinuumMatterVector_p506CoframeShear30
    field derivativeThree parameter]
  change
    (field.conjugateMatter
        (generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
            (withCoframe field 1) -
          (parameter / 8 : ℝ) • diracSpinZeroMatterProbe)).re =
      (field.conjugateMatter
          (generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
            (withCoframe field 1))).re -
        parameter / 8
  rw [conjugateMatter]
  rw [show
    (parameter / 8 : ℝ) • diracSpinZeroMatterProbe =
      ((parameter / 8 : ℝ) : ℂ) • diracSpinZeroMatterProbe by
    rfl]
  simp only [map_sub, map_smul, Complex.sub_re, Complex.smul_re]
  rw [diracSpinZeroMatterCoordinate_probe]
  norm_num

theorem coframeMatterSectorLocalDensity_p506CoframeShear30_hasDerivAt
    (field : StageNineContinuumPointField)
    (conjugateMatter :
      field.conjugateMatter =
        (diracSpinZeroMatterCoordinate :
          Module.Dual ℂ DiracExteriorMatterCarrier))
    (derivativeThree :
      field.matterCovariantDerivative 3 =
        (-(Complex.I / 8)) • diracSpinTwoMatterProbe) :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0 field
          (p506CoframeShear30 parameter))
      (-(1 / 8 : ℝ)) 0 := by
  have affineDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0 field
              1 -
            parameter / 8)
        (-(1 / 8 : ℝ)) 0 := by
    have scaled :=
      (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (1 / 8 : ℝ)
    have subtracted :=
      scaled.const_sub
        (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0 field 1)
    simpa [div_eq_mul_inv] using subtracted
  apply affineDerivative.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall
    (coframeMatterSectorLocalDensity_p506CoframeShear30
      field conjugateMatter derivativeThree)

/-! ## The generated P506 actual and its nonzero stress coordinate -/

/-- Origin field of the complete C3h149 local actual replay. -/
def positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField :
    StageNineContinuumPointField :=
  toContinuumPointField
    (positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift
      0 0) 0

theorem positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_coframe :
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.coframe =
      1 := by
  change
    (positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift
      0 0).coframe 0 = 1
  rw [
    positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift_zero]
  exact positiveP506MatterCurrentEinsteinCartanLocalActualLift_coframe 0

theorem
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_conjugate :
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.conjugateMatter =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier) := by
  change
    (positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift
      0 0).conjugateMatter 0 =
      (diracSpinZeroMatterCoordinate :
        Module.Dual ℂ DiracExteriorMatterCarrier)
  rw [
    positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift_zero]
  exact
    positiveP506MatterCurrentEinsteinCartanLocalActualLift_conjugate_origin

theorem positiveP506MatterCurrentEinsteinCartanCauchyState_matter_constant :
    positiveP506MatterCurrentEinsteinCartanCauchyState.matter =
      fun _ => diracSpinTwoMatterProbe := by
  funext space
  change (positiveP506MatterCurrentCartanTrajectoryState 0).matter space = _
  rw [positiveP506MatterCurrentCartanTrajectoryState_zero]
  change (positiveSourceTargetMatterCauchyState.matter) space = _
  change (positiveSourceTargetMatterCauchyState.matter) 0 = _
  exact positiveSourceTargetMatterCauchyState_matter

theorem positiveP506MatterCurrentEinsteinCartanCauchyState_gauge_zero :
    positiveP506MatterCurrentEinsteinCartanCauchyState.gaugeConnection = 0 := by
  change
    (positiveP506MatterCurrentCartanTrajectoryState 0).gaugeConnection = 0
  rw [positiveP506MatterCurrentCartanTrajectoryState_zero]
  change (positiveSourceTargetMatterCauchyState.gaugeConnection) = 0
  change (positivePhaseProbeCauchyState.gaugeConnection) = 0
  rw [positivePhaseProbeCauchyState_eq_normalForm]
  rfl

theorem
    positiveP506MatterCurrentEinsteinCartanCauchyState_gravity_origin :
    positiveP506MatterCurrentEinsteinCartanCauchyState.gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  exact
    (sourceActionGeneratedJointLocalActualLift_initialGravityConnection
      positiveSmoothUnifiedSource
      positiveP506MatterCurrentEinsteinCartanCauchyState 0).symm.trans
    positiveP506MatterCurrentEinsteinCartanLocalActualLift_connection_origin

theorem positiveP506MatterCurrentEinsteinCartan_spinLift_three :
    diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm
            positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
          (3 : LorentzianIndex))
        diracSpinTwoMatterProbe =
      (-(Complex.I / 8)) • diracSpinTwoMatterProbe := by
  rw [show
    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
      einsteinCartanSpinContorsionCoordinates
        positiveP506MatterCurrentEinsteinCartanSpinCoordinates by
    rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  funext spinIndex
  fin_cases spinIndex
  all_goals
    simp [diracSpinConnectionLift,
      loweredLorentzConnectionCoefficient_ofBivectorOneForm,
      einsteinCartanSpinContorsionCoordinates,
      positiveP506MatterCurrentSpinCoordinatesNormalForm,
      diracMatrixMatterAction, diracSpinTwoMatterProbe,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
      lorentzBivectorFirst, lorentzBivectorSecond,
      Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  all_goals norm_num
  all_goals try (congr 1; ring)

theorem
    positiveP506MatterCurrentEinsteinCartanCauchyState_spatialDerivative_two_zero :
    cauchyMatterSpatialDerivativeCoordinate
        positiveP506MatterCurrentEinsteinCartanCauchyState 0 2 =
      0 := by
  rw [cauchyMatterSpatialDerivativeCoordinate,
    positiveP506MatterCurrentEinsteinCartanCauchyState_matter_constant]
  simp

theorem
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_derivative_three :
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.matterCovariantDerivative
        3 =
      (-(Complex.I / 8)) • diracSpinTwoMatterProbe := by
  change
    holonomicMatterCovariantDerivative
        (positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift
          0 0) 0 3 =
      _
  rw [
    positiveP506MatterCurrentEinsteinCartanPrimitiveCauchyLocalActualLift_zero]
  change
    holonomicMatterCovariantDerivative
        (sourceActionGeneratedJointLocalActualLift
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentEinsteinCartanCauchyState 0)
        0 3 =
      _
  rw [
    sourceActionGeneratedJointLocalActualLift_matterCovariantDerivative_origin]
  rw [show (3 : LorentzianIndex) = (2 : Fin 3).succ by
    rfl,
    sourceActionGeneratedMatterLocalActualLift_spatialCovariantDerivative_origin]
  unfold cauchyMatterSpatialCovariantDerivative cauchyMatterConnectionAction
  rw [
    positiveP506MatterCurrentEinsteinCartanCauchyState_spatialDerivative_two_zero,
    positiveP506MatterCurrentEinsteinCartanCauchyState_matter_constant,
    positiveP506MatterCurrentEinsteinCartanCauchyState_gravity_origin,
    positiveP506MatterCurrentEinsteinCartanCauchyState_gauge_zero]
  simp [positiveP506MatterCurrentEinsteinCartan_spinLift_three]

/-- The actual matter stress covector read from the complete generated `U₁`. -/
def positiveP506MatterCurrentEinsteinCartanMatterStress :
    LorentzianCoframe →L[ℝ] ℝ :=
  coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField

theorem positiveP506MatterCurrentEinsteinCartanMatterStress_selected :
    positiveP506MatterCurrentEinsteinCartanMatterStress
        (coframeCoordinateDirection 3 0) =
      -(1 / 8 : ℝ) := by
  have nondegenerate :
      Matrix.det
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField.coframe ≠
        0 := by
    rw [
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_coframe]
    simp
  have actionDerivative :=
    coframeMatterSectorLocalDensity_hasFDerivAt positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
      nondegenerate
  rw [
    positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_coframe]
    at actionDerivative
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have coordinateDerivative :=
    identityDerivative.smul_const (coframeCoordinateDirection 3 0)
  have coordinateDerivativeValue :
      (1 : ℝ) • coframeCoordinateDirection 3 0 =
        coframeCoordinateDirection 3 0 := by
    simp
  have coordinateDerivativeAtZero :=
    coordinateDerivative.congr_deriv coordinateDerivativeValue
  have pathDerivative :=
    coordinateDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have pointEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • coframeCoordinateDirection 3 0 := by
    simp
  have composedDerivative :=
    actionDerivative.comp_hasDerivAt_of_eq
      (0 : ℝ) pathDerivative pointEquality
  have exactDerivative :=
    coframeMatterSectorLocalDensity_p506CoframeShear30_hasDerivAt
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_conjugate
      positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField_derivative_three
  have affineEqualsShear :
      Filter.EventuallyEq (nhds (0 : ℝ))
        (fun parameter : ℝ =>
          coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
            positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
            ((1 : LorentzianCoframe) +
              parameter • coframeCoordinateDirection 3 0))
        (fun parameter : ℝ =>
          coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
            positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
            (p506CoframeShear30 parameter)) :=
    Filter.Eventually.of_forall fun parameter => by
      exact congrArg
        (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField)
        (p506CoframeShear30_eq_identity_add parameter).symm
  have exactAffineDerivative :=
    exactDerivative.congr_of_eventuallyEq affineEqualsShear
  have derivativeEquality :=
    composedDerivative.unique (by
      simpa only [Function.comp_def, id_eq] using exactAffineDerivative)
  change
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentEinsteinCartanPrimitiveOriginField
        (coframeCoordinateDirection 3 0) =
      -(1 / 8 : ℝ)
  exact derivativeEquality

theorem positiveP506MatterCurrentEinsteinCartanMatterStress_nonzero :
    positiveP506MatterCurrentEinsteinCartanMatterStress ≠ 0 := by
  intro stressZero
  have selectedZero :=
    DFunLike.congr_fun stressZero (coframeCoordinateDirection 3 0)
  rw [
    positiveP506MatterCurrentEinsteinCartanMatterStress_selected]
    at selectedZero
  norm_num at selectedZero

end

end
  SaturationMonoid.PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCoframeStress
