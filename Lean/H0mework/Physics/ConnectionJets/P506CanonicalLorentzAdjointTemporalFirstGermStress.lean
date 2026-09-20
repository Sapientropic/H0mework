import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermSupport
import H0mework.Physics.ConnectionJets.P506CanonicalLorentzAdjointTemporalFirstGermFixedContactReadout
import H0mework.Physics.GravityResponse.CoframeNormalForm

/-!
# C3h197: exact P506/L0 coframe-stress coordinates

This module evaluates the fixed P506/L0 non-gravity coframe stress on the
tracefree diagonal and temporal-spatial coordinate variations used by the
C3h196 adjoint temporal-germ decision.  These are convention-locked action
readouts, not source parameters or response certificates.

The finite gauge, scalar, and matter variation calculations stay together so
their common P506 representation and action normalization cannot drift across
separate ad-hoc coordinate files.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open EmpiricalReferenceScaleCouplingBoundary
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEinsteinCartanSpinContorsionAction
open StageNineEnrichedProofFreeSource
open StageNineConjugateMatterActionTimeVelocity
open StageNineCoframeSectorStress
open StageNineCoframeVariation
open StageNineGlobalIntegratedAction
open StageNineGravityGaugeActionLocalActualLift
open StageNineHolonomicField
open StageNineGravityAlgebraicKeepResponseCoframeNormalForm
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLinearPlebanskiGravityCoupledCoframeActionResponse
open StageNineLorentzConnectionVariation
open StageNineMatterActionTimeVelocity
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCoframeStress
open StageNineSourceActionGeneratedP506MatterCurrentEinsteinCartanLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentGravityCoupledP286GaussLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentLinearPlebanskiSynchronizedLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionLine
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureScalarLocalStationarity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open StageNineQStarP286CoframeCoordinateClassification
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open SU7ExteriorBreakingYukawa

open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ## The one stress direction seen by the temporal first germ -/

/-- Trace-free temporal-vs-spatial coframe direction.  This is a readout
direction, not an extra jet or response datum. -/
def temporalTracefreeCoframeVariation : LorentzianCoframe :=
  Matrix.diagonal ![(3 / 4 : ℝ), -(1 / 4 : ℝ),
    -(1 / 4 : ℝ), -(1 / 4 : ℝ)]

def temporalTracefreeCoframePath (parameter : ℝ) : LorentzianCoframe :=
  (1 : LorentzianCoframe) +
    parameter • temporalTracefreeCoframeVariation

@[simp] theorem temporalTracefreeCoframeVariation_trace :
    Matrix.trace temporalTracefreeCoframeVariation = 0 := by
  simp [temporalTracefreeCoframeVariation, Matrix.trace,
    Fin.sum_univ_four]
  norm_num

theorem temporalTracefreeCoframePath_eq_diagonal (parameter : ℝ) :
    temporalTracefreeCoframePath parameter =
      Matrix.diagonal ![(1 + 3 * parameter / 4 : ℝ),
        1 - parameter / 4, 1 - parameter / 4,
        1 - parameter / 4] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [temporalTracefreeCoframePath,
      temporalTracefreeCoframeVariation, Matrix.diagonal_apply,
      Matrix.one_apply] <;>
    ring

theorem temporalTracefreeCoframePath_det (parameter : ℝ) :
    Matrix.det (temporalTracefreeCoframePath parameter) =
      (1 + 3 * parameter / 4) * (1 - parameter / 4) ^ 3 := by
  rw [temporalTracefreeCoframePath_eq_diagonal, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]
  ring

theorem temporalTracefreeCoframePath_inv
    (parameter : ℝ)
    (temporalNonzero : 1 + 3 * parameter / 4 ≠ 0)
    (spatialNonzero : 1 - parameter / 4 ≠ 0) :
    (temporalTracefreeCoframePath parameter)⁻¹ =
      Matrix.diagonal ![(1 + 3 * parameter / 4)⁻¹,
        (1 - parameter / 4)⁻¹, (1 - parameter / 4)⁻¹,
        (1 - parameter / 4)⁻¹] := by
  apply Matrix.inv_eq_left_inv
  rw [temporalTracefreeCoframePath_eq_diagonal]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      temporalNonzero, spatialNonzero]

private theorem stress_apply_of_path_hasDerivAt
    (density : LorentzianCoframe → ℝ)
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (outer : HasFDerivAt density stress (1 : LorentzianCoframe))
    (value : ℝ)
    (pathDerivative :
      HasDerivAt (fun parameter : ℝ =>
        density (temporalTracefreeCoframePath parameter)) value 0) :
    stress temporalTracefreeCoframeVariation = value := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const temporalTracefreeCoframeVariation
  have variationDerivativeValue :
      (1 : ℝ) • temporalTracefreeCoframeVariation =
        temporalTracefreeCoframeVariation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have affineDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • temporalTracefreeCoframeVariation := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 affineDerivative baseEquality
  have derivativeEquality := composed.unique (by
    simpa [temporalTracefreeCoframePath, Function.comp_def] using
      pathDerivative)
  exact derivativeEquality

/-! ### Vanishing scalar sector on the current contact -/

theorem matterResponseOrigin_scalarKinetic_withCoframe_zero
    (coframe : LorentzianCoframe) :
    generatedScalarKineticDensity positiveSmoothUnifiedSource 0 0
        (withCoframe positiveP506MatterCurrentMatterResponseOriginField
          coframe) = 0 := by
  unfold generatedScalarKineticDensity
  simp only [withCoframe]
  rw [matterResponseOrigin_scalarCovariantDerivative_zero]
  simp [scalarFrameRelativeCovariantDerivative,
    scalarCoordinatePairingRe]

theorem matterResponseOrigin_scalarPotential_zero :
    generatedScalarPotential positiveSmoothUnifiedSource 0 0
        positiveP506MatterCurrentMatterResponseOriginField.scalar = 0 := by
  rw [matterResponseOrigin_scalar_eq_vacuum]
  simp [generatedScalarPotential]

theorem matterResponseOrigin_scalarSectorLocalDensity_zero
    (coframe : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField coframe = 0 := by
  unfold coframeScalarSectorLocalDensity
  rw [matterResponseOrigin_scalarKinetic_withCoframe_zero,
    matterResponseOrigin_scalarPotential_zero]
  ring

theorem matterResponseOrigin_scalarSectorStress_zero :
    coframeScalarSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField = 0 := by
  unfold coframeScalarSectorStressCovector
  have densityZero :
      coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField = 0 := by
    funext coframe
    exact matterResponseOrigin_scalarSectorLocalDensity_zero coframe
  rw [densityZero]
  simp

/-! ### P286 gauge sector on the same single path -/

def matterResponseOriginCurvatureNormalForm : P286GaugeTwoForm :=
  ![(1 / 6 : ℝ) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    0, 0, 0, 0, 0]

def matterResponseOriginAuxiliaryNormalForm : P286GaugeTwoForm :=
  ![0, 0, 0,
    (1 / 3 : ℝ) •
      positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
    0, 0]

theorem matterResponseOrigin_auxiliaryCoordinate_normalForm :
    p286AuxiliaryCoordinate
        positiveP506MatterCurrentMatterResponseOriginField =
      matterResponseOriginAuxiliaryNormalForm := by
  funext pair
  change
    p286CoordinateEquiv
        (positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeAuxiliary
          0 pair) = _
  rw [positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeAuxiliary,
    positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeAuxiliary]
  change
    p286CoordinateEquiv
        (positiveP506MatterCurrentP286CompleteResponseLocalActualLift.gaugeAuxiliary
          0 pair) = _
  unfold positiveP506MatterCurrentP286CompleteResponseLocalActualLift
    installGeneratedGaugeAuxiliaryGerm
  simp only
  unfold positiveP506MatterCurrentP286CompleteResponseAuxiliaryField
  rw [p286CoordinateEquiv.apply_symm_apply,
    positiveP506MatterCurrentP286CompleteResponseAuxiliaryCoordinate_normalForm]
  fin_cases pair <;>
    simp [matterResponseOriginAuxiliaryNormalForm,
      c3h181FullAuxiliaryCoordinateNormalForm]

theorem matterResponseOrigin_curvatureCoordinate_normalForm :
    p286CurvatureCoordinate
        positiveP506MatterCurrentMatterResponseOriginField =
      matterResponseOriginCurvatureNormalForm := by
  funext pair
  change
    p286CoordinateEquiv
        (holonomicGaugeCurvature
          positiveP506MatterCurrentMatterResponseLocalActualLift 0 pair) = _
  rw [holonomicGaugeCurvature_eq_of_connection_eq_current
    positiveP506MatterCurrentMatterResponseLocalActualLift
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift
    (by
      rw [positiveP506MatterCurrentMatterResponseLocalActualLift_gaugeConnection,
        positiveP506MatterCurrentLorentzResponseLocalActualLift_gaugeConnection])]
  rw [
    positiveP506MatterCurrentP286CompleteResponseLocalActualLift_gaugeCurvature_origin,
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_gaugeCurvature]
  have coordinateForm := congrFun
    positiveP506MatterCurrentP286_actionGeneratedCurvature_coordinate pair
  rw [coordinateForm]
  rw [positiveP506MatterCurrentP286GaussCauchyState_coframe_axis,
    StageNineResidualLimitCoframeBalanceDecision.coframeGaugeSpacetimeHodgeLinear_one,
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half,
    liftGaugeTwoFormOperator_smul_operator_p286,
    positiveP506MatterCurrentP286GaussCauchyAuxiliaryCoordinate_normalForm]
  change
    (1 / 2 : ℝ) •
        liftGaugeTwoFormOperator lorentzianCoframeHodge
          ![0, 0, 0,
            (1 / 3 : ℝ) •
              positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge,
            0, 0] pair =
      matterResponseOriginCurvatureNormalForm pair
  rw [
    StageNineP286SourceAffineCurvatureJetNormalForm.liftGaugeTwoFormOperator_fixedHodge_apply_local]
  fin_cases pair <;>
    simp [matterResponseOriginCurvatureNormalForm, smul_smul]
  congr 1
  norm_num

theorem matterResponseOrigin_gaugeSectorLocalDensity_temporalTracefree
    (parameter : ℝ)
    (temporalNonzero : 1 + 3 * parameter / 4 ≠ 0)
    (spatialNonzero : 1 - parameter / 4 ≠ 0)
    (detPositive : 0 < Matrix.det
      (temporalTracefreeCoframePath parameter)) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField
        (temporalTracefreeCoframePath parameter) =
      (5 / 108 : ℝ) * (1 - parameter / 4) ^ 6 *
        (1 + 3 * parameter / 4) *
        ((1 - parameter / 4) - 2 * (1 + 3 * parameter / 4)) := by
  unfold coframeGaugeSectorLocalDensity
  dsimp only
  have couplingStrongWeak :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared := rfl
  have couplingStrongHypercharge :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared := rfl
  rw [← couplingStrongWeak, ← couplingStrongHypercharge]
  rw [← generatedGaugeSectorBFDensity_p286_decompose]
  rw [generatedGaugeSectorBFDensity_p286_eq_coordinate]
  rw [
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half]
  change
    generatedVolumeDensity
          (withCoframe positiveP506MatterCurrentMatterResponseOriginField
            (temporalTracefreeCoframePath parameter)) *
        generatedGaugeSectorBFDensity p286CoordinateLiePairing
          (temporalTracefreeCoframePath parameter)
          (coframeGaugeSpacetimeHodgeLinear
            (temporalTracefreeCoframePath parameter))
          ((1 / 2 : ℝ) • coframeGaugeSpacetimeHodgeLinear
            (temporalTracefreeCoframePath parameter))
          (p286CurvatureCoordinate
            positiveP506MatterCurrentMatterResponseOriginField)
          (p286AuxiliaryCoordinate
            positiveP506MatterCurrentMatterResponseOriginField) = _
  rw [matterResponseOrigin_curvatureCoordinate_normalForm,
    matterResponseOrigin_auxiliaryCoordinate_normalForm]
  unfold generatedVolumeDensity
  simp only [withCoframe]
  rw [abs_of_pos detPositive, temporalTracefreeCoframePath_det]
  unfold generatedGaugeSectorBFDensity coframeGaugeSpacetimeHodgeLinear
    inverseCoframeTwoFormLinear
  rw [temporalTracefreeCoframePath_inv parameter temporalNonzero spatialNonzero]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    temporalTracefreeCoframePath_eq_diagonal,
    generatedGaugeTwoFormMetricPairing,
    liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
    coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond,
    p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_add_right,
    p286CoordinateLiePairing_neg_left_local,
    p286CoordinateLiePairing_neg_right_local,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_right,
    currentGaussCharge_pairing_self,
    smul_smul,
    Fin.sum_univ_six, temporalNonzero, spatialNonzero] <;>
    field_simp [temporalNonzero, spatialNonzero] <;>
    ring_nf

private theorem temporalTracefreeCoframePath_regular_eventually :
    ∀ᶠ parameter : ℝ in nhds 0,
      1 + 3 * parameter / 4 ≠ 0 ∧
      1 - parameter / 4 ≠ 0 ∧
      0 < Matrix.det (temporalTracefreeCoframePath parameter) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (show (0 : ℝ) < 1 by norm_num)] with parameter inBall
  have absLt : |parameter| < 1 := by
    simpa [Real.dist_eq] using inBall
  rcases abs_lt.mp absLt with ⟨lower, upper⟩
  have temporalPositive : 0 < 1 + 3 * parameter / 4 := by
    nlinarith
  have spatialPositive : 0 < 1 - parameter / 4 := by
    nlinarith
  refine ⟨temporalPositive.ne', spatialPositive.ne', ?_⟩
  rw [temporalTracefreeCoframePath_det]
  exact mul_pos temporalPositive (pow_pos spatialPositive 3)

theorem matterResponseOrigin_gaugeSectorPath_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          positiveP506MatterCurrentMatterResponseOriginField
          (temporalTracefreeCoframePath parameter))
      (-(5 / 108 : ℝ)) 0 := by
  have polynomialDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          (5 / 108 : ℝ) * (1 - parameter / 4) ^ 6 *
            (1 + 3 * parameter / 4) *
            ((1 - parameter / 4) - 2 * (1 + 3 * parameter / 4)))
        (-(5 / 108 : ℝ)) 0 := by
    have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
    have temporalDerivative :=
      (identityDerivative.mul_const (3 / 4 : ℝ)).const_add 1
    have spatialDerivative :=
      (identityDerivative.mul_const (1 / 4 : ℝ)).const_sub 1
    have assembled :=
      (((spatialDerivative.pow 6).const_mul (5 / 108 : ℝ)).mul
        temporalDerivative).mul
          (spatialDerivative.sub (temporalDerivative.const_mul 2))
    norm_num [id_eq] at assembled
    apply assembled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun parameter => by simp; ring)
  apply polynomialDerivative.congr_of_eventuallyEq
  filter_upwards [temporalTracefreeCoframePath_regular_eventually]
      with parameter regular
  exact matterResponseOrigin_gaugeSectorLocalDensity_temporalTracefree
    parameter regular.1 regular.2.1 regular.2.2

theorem matterResponseOrigin_gaugeSectorStress_temporalTracefree :
    coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField
        temporalTracefreeCoframeVariation =
      -(5 / 108 : ℝ) := by
  have coframeOne :
      positiveP506MatterCurrentMatterResponseOriginField.coframe =
        (1 : LorentzianCoframe) := by
    change
      positiveP506MatterCurrentMatterResponseLocalActualLift.coframe 0 = 1
    rw [positiveP506MatterCurrentMatterResponseLocalActualLift_coframe,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_coframe]
    exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0
  have nondegenerate :
      Matrix.det
          positiveP506MatterCurrentMatterResponseOriginField.coframe ≠ 0 := by
    rw [coframeOne]
    simp
  exact stress_apply_of_path_hasDerivAt
    (coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField)
    (coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField)
    (by
      simpa [coframeOne] using
        coframeGaugeSectorLocalDensity_hasFDerivAt
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentMatterResponseOriginField
          nondegenerate)
    (-(5 / 108 : ℝ))
    matterResponseOrigin_gaugeSectorPath_hasDerivAt

/-! ### Matter sector on the same single path -/

theorem completeActualSpin_eq_einsteinCartan :
    positiveP506MatterCurrentCompleteActualSpin =
      positiveP506MatterCurrentEinsteinCartanSpinCoordinates := by
  unfold positiveP506MatterCurrentCompleteActualSpin
  calc
    actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          positiveP506MatterCurrentCompleteBaseActual 0 =
        actualMatterSpinActionCoordinates positiveSmoothUnifiedSource
          positiveP506MatterCurrentEinsteinCartanLocalActualLift 0 := by
      apply actualMatterSpinActionCoordinates_eq_of_origin_fields
      · rw [positiveP506MatterCurrentCompleteBaseActual_coframe_one,
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_coframe]
      · change positiveP506MatterCurrentCompleteBaseActual.matter 0 = _
        rw [
          positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.1,
          currentU7_matter_origin,
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_matter_origin]
      · change positiveP506MatterCurrentCompleteBaseActual.conjugateMatter 0 = _
        rw [
          positiveP506MatterCurrentP286CompleteResponseLocalActualLift_retainsU7Fields.2.2.2.2.2.2.2,
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_conjugate_origin,
          positiveP506MatterCurrentEinsteinCartanLocalActualLift_conjugate_origin]
    _ = _ :=
      positiveP506MatterCurrentEinsteinCartanLocalActualLift_spinCoordinates

theorem completeActualContorsion_eq_einsteinCartan :
    positiveP506MatterCurrentCompleteActualContorsion =
      positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  unfold positiveP506MatterCurrentCompleteActualContorsion
    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates
    sourceActionGeneratedCurrentEinsteinCartanContorsionCoordinates
  rw [completeActualSpin_eq_einsteinCartan]

theorem einsteinCartan_spatialKinetic_pairing :
    (diracSpinZeroMatterCoordinate
      (Complex.I •
        ∑ direction : Fin 3,
          diracMatrixMatterAction (diracGamma direction.succ)
            (diracMatrixMatterAction
              (diracSpinConnectionLift
                (lorentzSkewConnectionOfBivectorOneForm
                  positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
                direction.succ)
              diracSpinTwoMatterProbe))).re =
      (5 / 8 : ℝ) := by
  rw [show
    positiveP506MatterCurrentEinsteinCartanContorsionCoordinates =
      einsteinCartanSpinContorsionCoordinates
        positiveP506MatterCurrentEinsteinCartanSpinCoordinates by rfl,
    positiveP506MatterCurrentEinsteinCartanSpinCoordinates_eq_normalForm]
  simp [diracSpinConnectionLift,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm,
    einsteinCartanSpinContorsionCoordinates,
    positiveP506MatterCurrentSpinCoordinatesNormalForm,
    diracMatrixMatterAction, diracSpinTwoMatterProbe,
    diracSpinZeroMatterCoordinate,
    diracGamma, diracGammaZero, diracGammaOne,
    diracGammaTwo, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four,
    Fin.sum_univ_three,
    lorentzBivectorFirst, lorentzBivectorSecond,
    Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  norm_num

theorem lorentzResponseCauchyState_gravityConnection_origin_local :
    positiveP506MatterCurrentLorentzResponseCauchyState.gravityConnection 0 =
      lorentzSkewConnectionOfBivectorOneForm
        positiveP506MatterCurrentEinsteinCartanContorsionCoordinates := by
  unfold positiveP506MatterCurrentLorentzResponseCauchyState
    canonicalCauchyRestriction
  change
    positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
        (canonicalCauchySlicePoint 0 0) = _
  rw [canonicalCauchySlicePoint_zero_zero_local,
    positiveP506MatterCurrentLorentzResponseLocalActualLift_connection_origin]
  unfold positiveP506MatterCurrentCompleteActionLorentzOrigin
  rw [completeActualContorsion_eq_einsteinCartan]

theorem lorentzResponseCauchyState_spatialCovariantDerivative_local
    (direction : Fin 3) :
    cauchyMatterSpatialCovariantDerivative
        positiveP506MatterCurrentLorentzResponseCauchyState 0 direction =
      diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm
            positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
          direction.succ)
        diracSpinTwoMatterProbe := by
  have rawDerivativeZero :
      cauchyMatterSpatialDerivativeCoordinate
          positiveP506MatterCurrentLorentzResponseCauchyState 0 direction =
        0 := by
    rw [cauchyMatterSpatialDerivativeCoordinate,
      lorentzResponseCauchyState_matter_constant_local]
    simp
  unfold cauchyMatterSpatialCovariantDerivative cauchyMatterConnectionAction
  rw [rawDerivativeZero,
    lorentzResponseCauchyState_matter_constant_local,
    lorentzResponseCauchyState_gravityConnection_origin_local,
    lorentzResponseCauchyState_gaugeConnection_origin_zero_local]
  simp

theorem matterResponseOrigin_spatialCovariantDerivative_local
    (direction : Fin 3) :
    positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
        direction.succ =
      cauchyMatterSpatialCovariantDerivative
        positiveP506MatterCurrentLorentzResponseCauchyState 0 direction := by
  change
    holonomicMatterCovariantDerivative
        positiveP506MatterCurrentMatterResponseLocalActualLift 0
          direction.succ = _
  let comparison :=
    sourceActionGeneratedMatterLocalActualLift positiveSmoothUnifiedSource
      positiveP506MatterCurrentLorentzResponseCauchyState 0
  have matterFieldEq :
      positiveP506MatterCurrentMatterResponseLocalActualLift.matter =
        comparison.matter := by
    rfl
  have gravityOriginEq :
      positiveP506MatterCurrentMatterResponseLocalActualLift.gravityConnection
          0 =
        comparison.gravityConnection 0 := by
    calc
      positiveP506MatterCurrentMatterResponseLocalActualLift.gravityConnection
            0 =
          positiveP506MatterCurrentLorentzResponseCauchyState.gravityConnection
            0 := by
        unfold positiveP506MatterCurrentLorentzResponseCauchyState
          canonicalCauchyRestriction
        change
          positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
              0 =
            positiveP506MatterCurrentLorentzResponseLocalActualLift.gravityConnection
              (canonicalCauchySlicePoint 0 0)
        rw [canonicalCauchySlicePoint_zero_zero_local]
      _ = comparison.gravityConnection 0 := by
        exact (sourceActionGeneratedGravityGaugeLocalActualLift_gravityConnection_origin
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentLorentzResponseCauchyState 0).symm
  have gaugeOriginEq :
      positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection 0 =
        comparison.gaugeConnection 0 := by
    calc
      positiveP506MatterCurrentMatterResponseLocalActualLift.gaugeConnection 0 =
          positiveP506MatterCurrentLorentzResponseCauchyState.gaugeConnection
            0 := by
        unfold positiveP506MatterCurrentLorentzResponseCauchyState
          canonicalCauchyRestriction
        change
          positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection
              0 =
            positiveP506MatterCurrentLorentzResponseLocalActualLift.gaugeConnection
              (canonicalCauchySlicePoint 0 0)
        rw [canonicalCauchySlicePoint_zero_zero_local]
      _ = comparison.gaugeConnection 0 := by
        funext direction
        exact (sourceGeneratedP286ActionLocalConnection_origin
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentLorentzResponseCauchyState 0 direction).symm
  calc
    holonomicMatterCovariantDerivative
          positiveP506MatterCurrentMatterResponseLocalActualLift 0
            direction.succ =
        holonomicMatterCovariantDerivative comparison 0 direction.succ := by
      unfold holonomicMatterCovariantDerivative
      rw [matterFieldEq, gravityOriginEq, gaugeOriginEq]
    _ = _ :=
      sourceActionGeneratedMatterLocalActualLift_spatialCovariantDerivative_origin
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentLorentzResponseCauchyState 0 direction

theorem matterResponseOrigin_spatialCovariantDerivative_normalForm
    (direction : Fin 3) :
    positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
        direction.succ =
      diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm
            positiveP506MatterCurrentEinsteinCartanContorsionCoordinates)
          direction.succ)
        diracSpinTwoMatterProbe := by
  rw [matterResponseOrigin_spatialCovariantDerivative_local,
    lorentzResponseCauchyState_spatialCovariantDerivative_local]

def matterResponseOriginTemporalVector : DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 0)
      (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
        0)

def matterResponseOriginSpatialVector : DiracExteriorMatterCarrier :=
  Complex.I •
    ∑ direction : Fin 3,
      diracMatrixMatterAction (diracGamma direction.succ)
        (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
          direction.succ)

def matterResponseOriginYukawaVector : DiracExteriorMatterCarrier :=
  chiralExteriorYukawaAction
    (scalarCoordinateEquiv.symm
      positiveP506MatterCurrentMatterResponseOriginField.scalar)
    positiveP506MatterCurrentMatterResponseOriginField.matter

def matterResponseOriginTemporalKinetic : ℝ :=
  (positiveP506MatterCurrentMatterResponseOriginField.conjugateMatter
    matterResponseOriginTemporalVector).re

def matterResponseOriginSpatialKinetic : ℝ :=
  (positiveP506MatterCurrentMatterResponseOriginField.conjugateMatter
    matterResponseOriginSpatialVector).re

def matterResponseOriginYukawa : ℝ :=
  (positiveP506MatterCurrentMatterResponseOriginField.conjugateMatter
    matterResponseOriginYukawaVector).re

theorem matterResponseOriginSpatialKinetic_eq :
    matterResponseOriginSpatialKinetic = (5 / 8 : ℝ) := by
  unfold matterResponseOriginSpatialKinetic
    matterResponseOriginSpatialVector
  rw [matterResponseOrigin_conjugate_probe]
  simp_rw [matterResponseOrigin_spatialCovariantDerivative_normalForm]
  exact einsteinCartan_spatialKinetic_pairing

theorem matterResponseOriginYukawa_eq_zero :
    matterResponseOriginYukawa = 0 := by
  unfold matterResponseOriginYukawa
    matterResponseOriginYukawaVector
  rw [matterResponseOrigin_conjugate_probe,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]
  rfl

theorem matterResponseOrigin_generatedContinuumMatterVector_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        positiveP506MatterCurrentMatterResponseOriginField = 0 := by
  have coframeEq :
      positiveP506MatterCurrentFullSynchronizedOriginField.coframe =
        positiveP506MatterCurrentMatterResponseOriginField.coframe := by
    rfl
  have scalarEq :
      positiveP506MatterCurrentFullSynchronizedOriginField.scalar =
        positiveP506MatterCurrentMatterResponseOriginField.scalar := by
    rfl
  have matterEq :
      positiveP506MatterCurrentFullSynchronizedOriginField.matter =
        positiveP506MatterCurrentMatterResponseOriginField.matter := by
    rfl
  have derivativeEq :
      positiveP506MatterCurrentFullSynchronizedOriginField.matterCovariantDerivative =
        positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative := by
    funext direction
    change
      holonomicMatterCovariantDerivative
          positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift 0
            direction =
        holonomicMatterCovariantDerivative
          positiveP506MatterCurrentMatterResponseLocalActualLift 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_matter,
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_gaugeConnection,
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_connection_origin,
      positiveP506MatterCurrentMatterResponseLocalActualLift_gravityConnection,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_connection_origin]
  calc
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          positiveP506MatterCurrentMatterResponseOriginField =
        generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          positiveP506MatterCurrentFullSynchronizedOriginField := by
      unfold generatedContinuumMatterVector
      rw [coframeEq, scalarEq, matterEq, derivativeEq]
    _ = 0 :=
      positiveP506MatterCurrentFullSynchronizedResponseLocalActualLift_diracYukawa_origin

theorem matterResponseOrigin_generatedContinuumMatterVector_decomposition :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        positiveP506MatterCurrentMatterResponseOriginField =
      matterResponseOriginTemporalVector +
        matterResponseOriginSpatialVector +
        matterResponseOriginYukawaVector := by
  unfold generatedContinuumMatterVector
  simp only [matterFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  have coframeOne :
      positiveP506MatterCurrentMatterResponseOriginField.coframe =
        (1 : LorentzianCoframe) := by
    change positiveP506MatterCurrentCompleteBaseActual.coframe 0 = 1
    exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0
  rw [coframeOne]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold matterResponseOriginTemporalVector
    matterResponseOriginSpatialVector matterResponseOriginYukawaVector
  simp [Fin.sum_univ_four, Fin.sum_univ_three]
  module

theorem matterResponseOrigin_kinetic_onShell :
    matterResponseOriginTemporalKinetic +
        matterResponseOriginSpatialKinetic +
        matterResponseOriginYukawa = 0 := by
  have vectorSumZero :
      matterResponseOriginTemporalVector +
          matterResponseOriginSpatialVector +
          matterResponseOriginYukawaVector = 0 := by
    rw [← matterResponseOrigin_generatedContinuumMatterVector_decomposition]
    exact matterResponseOrigin_generatedContinuumMatterVector_zero
  have paired := congrArg
    positiveP506MatterCurrentMatterResponseOriginField.conjugateMatter
    vectorSumZero
  simp only [map_add, map_zero] at paired
  have realPart := congrArg Complex.re paired
  unfold matterResponseOriginTemporalKinetic
    matterResponseOriginSpatialKinetic matterResponseOriginYukawa
  simpa only [Complex.add_re, Complex.zero_re] using realPart

theorem matterResponseOriginTemporalKinetic_eq :
    matterResponseOriginTemporalKinetic = -(5 / 8 : ℝ) := by
  have onShell := matterResponseOrigin_kinetic_onShell
  rw [matterResponseOriginSpatialKinetic_eq,
    matterResponseOriginYukawa_eq_zero] at onShell
  linarith

theorem inverseCoframeDiracGamma_temporalTracefreeCoframePath
    (parameter : ℝ)
    (temporalNonzero : 1 + 3 * parameter / 4 ≠ 0)
    (spatialNonzero : 1 - parameter / 4 ≠ 0)
    (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := temporalTracefreeCoframePath parameter,
          derivative := 0 }
        direction =
      ![(((1 + 3 * parameter / 4)⁻¹ : ℝ) : ℂ) • diracGamma 0,
        (((1 - parameter / 4)⁻¹ : ℝ) : ℂ) • diracGamma 1,
        (((1 - parameter / 4)⁻¹ : ℝ) : ℂ) • diracGamma 2,
        (((1 - parameter / 4)⁻¹ : ℝ) : ℂ) • diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [temporalTracefreeCoframePath_inv parameter temporalNonzero
    spatialNonzero]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [Matrix.diagonal_apply, diracGamma,
      diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four]

theorem matterResponseOrigin_generatedContinuumMatterVector_temporalTracefree
    (parameter : ℝ)
    (temporalNonzero : 1 + 3 * parameter / 4 ≠ 0)
    (spatialNonzero : 1 - parameter / 4 ≠ 0) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe positiveP506MatterCurrentMatterResponseOriginField
          (temporalTracefreeCoframePath parameter)) =
      (((1 + 3 * parameter / 4)⁻¹ : ℝ) : ℂ) •
          matterResponseOriginTemporalVector +
        (((1 - parameter / 4)⁻¹ : ℝ) : ℂ) •
          matterResponseOriginSpatialVector +
        matterResponseOriginYukawaVector := by
  unfold generatedContinuumMatterVector
  simp only [withCoframe, matterFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  simp_rw [inverseCoframeDiracGamma_temporalTracefreeCoframePath
    parameter temporalNonzero spatialNonzero]
  unfold matterResponseOriginTemporalVector
    matterResponseOriginSpatialVector matterResponseOriginYukawaVector
  simp [Fin.sum_univ_four, Fin.sum_univ_three,
    diracMatrixMatterAction_smul_matrix]
  module

theorem matterResponseOrigin_generatedContinuumMatterDensity_temporalTracefree
    (parameter : ℝ)
    (temporalNonzero : 1 + 3 * parameter / 4 ≠ 0)
    (spatialNonzero : 1 - parameter / 4 ≠ 0) :
    generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
        (withCoframe positiveP506MatterCurrentMatterResponseOriginField
          (temporalTracefreeCoframePath parameter)) =
      (1 + 3 * parameter / 4)⁻¹ *
          matterResponseOriginTemporalKinetic +
        (1 - parameter / 4)⁻¹ *
          matterResponseOriginSpatialKinetic +
        matterResponseOriginYukawa := by
  unfold generatedContinuumMatterDensity
  rw [matterResponseOrigin_generatedContinuumMatterVector_temporalTracefree
    parameter temporalNonzero spatialNonzero]
  simp only [withCoframe, matterDualFrameRelative_zeroChart]
  simp only [map_add, map_smul, Complex.add_re, Complex.coe_smul,
    Complex.smul_re]
  unfold matterResponseOriginTemporalKinetic
    matterResponseOriginSpatialKinetic matterResponseOriginYukawa
  simp only [smul_eq_mul]

theorem matterResponseOrigin_matterSectorLocalDensity_temporalTracefree
    (parameter : ℝ)
    (temporalNonzero : 1 + 3 * parameter / 4 ≠ 0)
    (spatialNonzero : 1 - parameter / 4 ≠ 0)
    (detPositive : 0 < Matrix.det
      (temporalTracefreeCoframePath parameter)) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField
        (temporalTracefreeCoframePath parameter) =
      (5 / 8 : ℝ) * parameter * (1 - parameter / 4) ^ 2 := by
  unfold coframeMatterSectorLocalDensity
  rw [matterResponseOrigin_generatedContinuumMatterDensity_temporalTracefree
      parameter temporalNonzero spatialNonzero,
    show generatedVolumeDensity
        (withCoframe positiveP506MatterCurrentMatterResponseOriginField
          (temporalTracefreeCoframePath parameter)) =
        |Matrix.det (temporalTracefreeCoframePath parameter)| by rfl,
    abs_of_pos detPositive, temporalTracefreeCoframePath_det,
    matterResponseOriginTemporalKinetic_eq,
    matterResponseOriginSpatialKinetic_eq,
    matterResponseOriginYukawa_eq_zero]
  rw [show
    (1 + 3 * parameter / 4) * (1 - parameter / 4) ^ 3 *
        ((1 + 3 * parameter / 4)⁻¹ * (-(5 / 8 : ℝ)) +
          (1 - parameter / 4)⁻¹ * (5 / 8 : ℝ) + 0) =
      ((1 + 3 * parameter / 4) *
          (1 + 3 * parameter / 4)⁻¹) *
          (1 - parameter / 4) ^ 3 * (-(5 / 8 : ℝ)) +
        (1 + 3 * parameter / 4) *
          ((1 - parameter / 4) *
            (1 - parameter / 4)⁻¹) *
          (1 - parameter / 4) ^ 2 * (5 / 8 : ℝ) by ring]
  rw [mul_inv_cancel₀ temporalNonzero,
    mul_inv_cancel₀ spatialNonzero]
  ring

theorem matterResponseOrigin_matterSectorPath_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField
          (temporalTracefreeCoframePath parameter))
      (5 / 8 : ℝ) 0 := by
  have polynomialDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          (5 / 8 : ℝ) * parameter * (1 - parameter / 4) ^ 2)
        (5 / 8 : ℝ) 0 := by
    have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
    have spatialDerivative :=
      (identityDerivative.mul_const (1 / 4 : ℝ)).const_sub 1
    have assembled :=
      (identityDerivative.const_mul (5 / 8 : ℝ)).mul
        (spatialDerivative.pow 2)
    norm_num [id_eq] at assembled
    apply assembled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => by
      simp only [Pi.mul_apply, Pi.pow_apply]
      ring)
  apply polynomialDerivative.congr_of_eventuallyEq
  filter_upwards [temporalTracefreeCoframePath_regular_eventually]
      with parameter regular
  exact matterResponseOrigin_matterSectorLocalDensity_temporalTracefree
    parameter regular.1 regular.2.1 regular.2.2

theorem matterResponseOrigin_matterSectorStress_temporalTracefree :
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField
        temporalTracefreeCoframeVariation =
      (5 / 8 : ℝ) := by
  have coframeOne :
      positiveP506MatterCurrentMatterResponseOriginField.coframe =
        (1 : LorentzianCoframe) := by
    change
      positiveP506MatterCurrentMatterResponseLocalActualLift.coframe 0 = 1
    rw [positiveP506MatterCurrentMatterResponseLocalActualLift_coframe,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_coframe]
    exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0
  have nondegenerate :
      Matrix.det
          positiveP506MatterCurrentMatterResponseOriginField.coframe ≠ 0 := by
    rw [coframeOne]
    simp
  exact stress_apply_of_path_hasDerivAt
    (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField)
    (coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField)
    (by
      simpa [coframeOne] using
        coframeMatterSectorLocalDensity_hasFDerivAt
          positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField
          nondegenerate)
    (5 / 8 : ℝ)
    matterResponseOrigin_matterSectorPath_hasDerivAt

theorem positiveP506MatterCurrentFullNonGravityCoframeStress_temporalTracefree :
    positiveP506MatterCurrentFullNonGravityCoframeStress
        temporalTracefreeCoframeVariation =
      (125 / 216 : ℝ) := by
  unfold positiveP506MatterCurrentFullNonGravityCoframeStress
  simp only [ContinuousLinearMap.add_apply]
  rw [matterResponseOrigin_gaugeSectorStress_temporalTracefree,
    matterResponseOrigin_scalarSectorStress_zero,
    matterResponseOrigin_matterSectorStress_temporalTracefree]
  norm_num

/-! ### The temporal--spatial `E03` shear seen by the response transpose -/

/-- The fixed `E03` coframe direction.  Like the trace-free direction above,
this is only a post-construction action readout and is not source data. -/
def temporalSpatial03CoframeVariation : LorentzianCoframe :=
  coframeCoordinateDirection 0 3

def temporalSpatial03CoframePath (parameter : ℝ) : LorentzianCoframe :=
  Matrix.transvection (0 : Fin 4) (3 : Fin 4) parameter

@[simp] theorem temporalSpatial03CoframePath_det (parameter : ℝ) :
    Matrix.det (temporalSpatial03CoframePath parameter) = 1 := by
  change
    Matrix.det
        (Matrix.transvection (0 : Fin 4) (3 : Fin 4) parameter) =
      1
  exact Matrix.det_transvection_of_ne (R := ℝ)
    (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide) parameter

theorem temporalSpatial03CoframePath_inverse (parameter : ℝ) :
    (temporalSpatial03CoframePath parameter)⁻¹ =
      temporalSpatial03CoframePath (-parameter) := by
  apply Matrix.inv_eq_left_inv
  change
    Matrix.transvection (0 : Fin 4) (3 : Fin 4) (-parameter) *
        Matrix.transvection (0 : Fin 4) (3 : Fin 4) parameter =
      1
  simpa using
    (Matrix.transvection_mul_transvection_same (R := ℝ)
      (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
      (-parameter) parameter)

theorem temporalSpatial03CoframePath_eq_identity_add (parameter : ℝ) :
    temporalSpatial03CoframePath parameter =
      (1 : LorentzianCoframe) +
        parameter • temporalSpatial03CoframeVariation := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [temporalSpatial03CoframePath,
      temporalSpatial03CoframeVariation, Matrix.transvection,
      coframeCoordinateDirection]

theorem inverseCoframeDiracGamma_temporalSpatial03CoframePath
    (parameter : ℝ) (direction : LorentzianIndex) :
    inverseCoframeDiracGamma
        { coframe := temporalSpatial03CoframePath parameter,
          derivative := 0 }
        direction =
      ![diracGamma 0 - (parameter : ℂ) • diracGamma 3,
        diracGamma 1, diracGamma 2, diracGamma 3] direction := by
  unfold inverseCoframeDiracGamma
  rw [temporalSpatial03CoframePath_inverse]
  fin_cases direction <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [temporalSpatial03CoframePath, Matrix.transvection,
      diracGamma, diracGammaZero, diracGammaOne,
      diracGammaTwo, diracGammaThree, Fin.sum_univ_four] <;>
    ring

private theorem stress_apply_of_temporalSpatial03Path_hasDerivAt
    (density : LorentzianCoframe → ℝ)
    (stress : LorentzianCoframe →L[ℝ] ℝ)
    (outer : HasFDerivAt density stress (1 : LorentzianCoframe))
    (value : ℝ)
    (pathDerivative :
      HasDerivAt (fun parameter : ℝ =>
        density (temporalSpatial03CoframePath parameter)) value 0) :
    stress temporalSpatial03CoframeVariation = value := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have variationDerivative :=
    identityDerivative.smul_const temporalSpatial03CoframeVariation
  have variationDerivativeValue :
      (1 : ℝ) • temporalSpatial03CoframeVariation =
        temporalSpatial03CoframeVariation := by
    simp
  have variationDerivativeAtZero :=
    variationDerivative.congr_deriv variationDerivativeValue
  have affineDerivative :=
    variationDerivativeAtZero.const_add (1 : LorentzianCoframe)
  have baseEquality :
      (1 : LorentzianCoframe) =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • temporalSpatial03CoframeVariation := by
    simp
  have composed :=
    outer.comp_hasDerivAt_of_eq 0 affineDerivative baseEquality
  have derivativeEquality := composed.unique (by
    simpa [temporalSpatial03CoframePath_eq_identity_add,
      Function.comp_def] using pathDerivative)
  exact derivativeEquality

/-! #### Gauge sector: only an even shear correction -/

theorem matterResponseOrigin_gaugeSectorLocalDensity_temporalSpatial03
    (parameter : ℝ) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField
        (temporalSpatial03CoframePath parameter) =
      -(5 / 108 : ℝ) * (1 + parameter ^ 2) := by
  unfold coframeGaugeSectorLocalDensity
  dsimp only
  have couplingStrongWeak :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared := rfl
  have couplingStrongHypercharge :
      (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared =
        (sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared := rfl
  rw [← couplingStrongWeak, ← couplingStrongHypercharge]
  rw [← generatedGaugeSectorBFDensity_p286_decompose]
  rw [generatedGaugeSectorBFDensity_p286_eq_coordinate]
  rw [
    StageNineResidualLimitCoframeBalanceDecision.positiveSource_generatedGaugeCoupling_eq_half]
  change
    generatedVolumeDensity
          (withCoframe positiveP506MatterCurrentMatterResponseOriginField
            (temporalSpatial03CoframePath parameter)) *
        generatedGaugeSectorBFDensity p286CoordinateLiePairing
          (temporalSpatial03CoframePath parameter)
          (coframeGaugeSpacetimeHodgeLinear
            (temporalSpatial03CoframePath parameter))
          ((1 / 2 : ℝ) • coframeGaugeSpacetimeHodgeLinear
            (temporalSpatial03CoframePath parameter))
          (p286CurvatureCoordinate
            positiveP506MatterCurrentMatterResponseOriginField)
          (p286AuxiliaryCoordinate
            positiveP506MatterCurrentMatterResponseOriginField) = _
  rw [matterResponseOrigin_curvatureCoordinate_normalForm,
    matterResponseOrigin_auxiliaryCoordinate_normalForm]
  unfold generatedVolumeDensity
  simp only [withCoframe, temporalSpatial03CoframePath_det, abs_one]
  unfold generatedGaugeSectorBFDensity coframeGaugeSpacetimeHodgeLinear
    inverseCoframeTwoFormLinear
  rw [temporalSpatial03CoframePath_inverse]
  simp [matterResponseOriginCurvatureNormalForm,
    matterResponseOriginAuxiliaryNormalForm,
    temporalSpatial03CoframePath, Matrix.transvection,
    generatedGaugeTwoFormMetricPairing,
    liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
    coframeTwoFormLinear, coframeWedge,
    lorentzianCoframeHodgeEquiv, lorentzianCoframeHodge,
    lorentzianTwoFormSign, minkowskiInternalSign,
    pairFirst, pairSecond,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_right,
    currentGaussCharge_pairing_self,
    Fin.sum_univ_six, Fin.coe_ofNat_eq_mod,
    Matrix.cons_val, Matrix.one_apply, Nat.reduceMod]
  simp only [p286CoordinateLiePairing_add_left,
    p286CoordinateLiePairing_add_right,
    p286CoordinateLiePairing_neg_left_local,
    p286CoordinateLiePairing_neg_right_local,
    p286CoordinateLiePairing_smul_left,
    p286CoordinateLiePairing_smul_right,
    currentGaussCharge_pairing_self, smul_smul]
  ring

theorem matterResponseOrigin_gaugeSectorPath_temporalSpatial03_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
          positiveP506MatterCurrentMatterResponseOriginField
          (temporalSpatial03CoframePath parameter))
      0 0 := by
  have polynomialDerivative :
      HasDerivAt
        (fun parameter : ℝ => -(5 / 108 : ℝ) * (1 + parameter ^ 2))
        0 0 := by
    have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
    have assembled :=
      ((identityDerivative.pow 2).const_add 1).const_mul
        (-(5 / 108 : ℝ))
    norm_num [id_eq] at assembled
    apply assembled.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun parameter => by simp)
  apply polynomialDerivative.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun parameter =>
    matterResponseOrigin_gaugeSectorLocalDensity_temporalSpatial03 parameter

theorem matterResponseOrigin_gaugeSectorStress_temporalSpatial03 :
    coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
        positiveP506MatterCurrentMatterResponseOriginField
        temporalSpatial03CoframeVariation =
      0 := by
  have coframeOne :
      positiveP506MatterCurrentMatterResponseOriginField.coframe =
        (1 : LorentzianCoframe) := by
    change
      positiveP506MatterCurrentMatterResponseLocalActualLift.coframe 0 = 1
    rw [positiveP506MatterCurrentMatterResponseLocalActualLift_coframe,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_coframe]
    exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0
  have nondegenerate :
      Matrix.det
          positiveP506MatterCurrentMatterResponseOriginField.coframe ≠ 0 := by
    rw [coframeOne]
    simp
  exact stress_apply_of_temporalSpatial03Path_hasDerivAt
    (coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField)
    (coframeGaugeSectorStressCovector positiveSmoothUnifiedSource
      positiveP506MatterCurrentMatterResponseOriginField)
    (by
      simpa [coframeOne] using
        coframeGaugeSectorLocalDensity_hasFDerivAt
          positiveSmoothUnifiedSource
          positiveP506MatterCurrentMatterResponseOriginField
          nondegenerate)
    0 matterResponseOrigin_gaugeSectorPath_temporalSpatial03_hasDerivAt

/-! #### Matter sector: the temporal kinetic fixes the sign -/

def matterResponseOriginTemporalSpatial03Vector :
    DiracExteriorMatterCarrier :=
  Complex.I •
    diracMatrixMatterAction (diracGamma 3)
      (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
        0)

def matterResponseOriginTemporalSpatial03Kinetic : ℝ :=
  (positiveP506MatterCurrentMatterResponseOriginField.conjugateMatter
    matterResponseOriginTemporalSpatial03Vector).re

theorem diracSpinZeroMatterCoordinate_gammaThree_eq_gammaZero
    (matter : DiracExteriorMatterCarrier) :
    diracSpinZeroMatterCoordinate
        (diracMatrixMatterAction (diracGamma 3) matter) =
      diracSpinZeroMatterCoordinate
        (diracMatrixMatterAction (diracGamma 0) matter) := by
  simp [diracSpinZeroMatterCoordinate,
    hyperchargeDegreeTwoMatterCoordinate,
    diracMatrixMatterAction, diracGamma,
    diracGammaZero, diracGammaThree,
    Matrix.mul_apply, Fin.sum_univ_four]

theorem matterResponseOriginTemporalSpatial03Kinetic_eq_temporal :
    matterResponseOriginTemporalSpatial03Kinetic =
      matterResponseOriginTemporalKinetic := by
  unfold matterResponseOriginTemporalSpatial03Kinetic
    matterResponseOriginTemporalSpatial03Vector
    matterResponseOriginTemporalKinetic matterResponseOriginTemporalVector
  rw [matterResponseOrigin_conjugate_probe]
  simp only [map_smul]
  rw [diracSpinZeroMatterCoordinate_gammaThree_eq_gammaZero]

theorem matterResponseOriginTemporalSpatial03Kinetic_eq :
    matterResponseOriginTemporalSpatial03Kinetic = -(5 / 8 : ℝ) := by
  rw [matterResponseOriginTemporalSpatial03Kinetic_eq_temporal,
    matterResponseOriginTemporalKinetic_eq]

theorem matterResponseOrigin_generatedContinuumMatterVector_temporalSpatial03
    (parameter : ℝ) :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (withCoframe positiveP506MatterCurrentMatterResponseOriginField
          (temporalSpatial03CoframePath parameter)) =
      generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
          (withCoframe positiveP506MatterCurrentMatterResponseOriginField 1) -
        (parameter : ℂ) • matterResponseOriginTemporalSpatial03Vector := by
  unfold generatedContinuumMatterVector
  simp only [withCoframe, matterFrameRelative_zeroChart,
    matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart]
  simp_rw [inverseCoframeDiracGamma_temporalSpatial03CoframePath]
  simp_rw [show
    ({ coframe := (1 : LorentzianCoframe), derivative := 0 } :
      PointwiseLorentzianCoframeJet) = identityCoframeMatterGeometry by rfl,
    inverseCoframeDiracGamma_identity]
  unfold matterResponseOriginTemporalSpatial03Vector
  simp only [Fin.sum_univ_four]
  change
    Complex.I •
          (diracMatrixMatterAction
                (diracGamma 0 - (parameter : ℂ) • diracGamma 3)
                (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                  0) +
              diracMatrixMatterAction (diracGamma 1)
                (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                  1) +
            diracMatrixMatterAction (diracGamma 2)
              (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                2) +
          diracMatrixMatterAction (diracGamma 3)
            (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
              3)) +
        chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm
            positiveP506MatterCurrentMatterResponseOriginField.scalar)
          positiveP506MatterCurrentMatterResponseOriginField.matter =
      Complex.I •
            (diracMatrixMatterAction (diracGamma 0)
                  (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                    0) +
                diracMatrixMatterAction (diracGamma 1)
                  (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                    1) +
              diracMatrixMatterAction (diracGamma 2)
                (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                  2) +
            diracMatrixMatterAction (diracGamma 3)
              (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                3)) +
          chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm
              positiveP506MatterCurrentMatterResponseOriginField.scalar)
            positiveP506MatterCurrentMatterResponseOriginField.matter -
        (parameter : ℂ) •
          (Complex.I •
            diracMatrixMatterAction (diracGamma 3)
              (positiveP506MatterCurrentMatterResponseOriginField.matterCovariantDerivative
                0))
  rw [diracMatrixMatterAction_sub_smul_matrix]
  module

theorem matterResponseOrigin_generatedContinuumMatterDensity_temporalSpatial03
    (parameter : ℝ) :
    generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
        (withCoframe positiveP506MatterCurrentMatterResponseOriginField
          (temporalSpatial03CoframePath parameter)) =
      generatedContinuumMatterDensity positiveSmoothUnifiedSource 0 0
          (withCoframe positiveP506MatterCurrentMatterResponseOriginField 1) -
        parameter * matterResponseOriginTemporalSpatial03Kinetic := by
  unfold generatedContinuumMatterDensity
  rw [matterResponseOrigin_generatedContinuumMatterVector_temporalSpatial03]
  simp only [withCoframe, matterDualFrameRelative_zeroChart,
    map_sub, map_smul, Complex.sub_re, Complex.smul_re]
  unfold matterResponseOriginTemporalSpatial03Kinetic
  simp [smul_eq_mul, Complex.mul_re]

theorem matterResponseOrigin_matterSectorLocalDensity_temporalSpatial03
    (parameter : ℝ) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField
        (temporalSpatial03CoframePath parameter) =
      coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField 1 +
        (5 / 8 : ℝ) * parameter := by
  unfold coframeMatterSectorLocalDensity generatedVolumeDensity
  rw [matterResponseOrigin_generatedContinuumMatterDensity_temporalSpatial03]
  simp only [withCoframe]
  rw [temporalSpatial03CoframePath_det, Matrix.det_one,
    abs_one, one_mul,
    matterResponseOriginTemporalSpatial03Kinetic_eq]
  ring

theorem matterResponseOrigin_matterSectorPath_temporalSpatial03_hasDerivAt :
    HasDerivAt
      (fun parameter : ℝ =>
        coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField
          (temporalSpatial03CoframePath parameter))
      (5 / 8 : ℝ) 0 := by
  have affineDerivative :
      HasDerivAt
        (fun parameter : ℝ =>
          coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
              positiveP506MatterCurrentMatterResponseOriginField 1 +
            (5 / 8 : ℝ) * parameter)
        (5 / 8 : ℝ) 0 := by
    have scaled :=
      (hasDerivAt_id (x := (0 : ℝ))).const_mul (5 / 8 : ℝ)
    have assembled := scaled.const_add
      (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField 1)
    simpa only [id_eq, mul_one] using assembled
  apply affineDerivative.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun parameter =>
    matterResponseOrigin_matterSectorLocalDensity_temporalSpatial03 parameter

theorem matterResponseOrigin_matterSectorStress_temporalSpatial03 :
    coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
        positiveP506MatterCurrentMatterResponseOriginField
        temporalSpatial03CoframeVariation =
      (5 / 8 : ℝ) := by
  have coframeOne :
      positiveP506MatterCurrentMatterResponseOriginField.coframe =
        (1 : LorentzianCoframe) := by
    change
      positiveP506MatterCurrentMatterResponseLocalActualLift.coframe 0 = 1
    rw [positiveP506MatterCurrentMatterResponseLocalActualLift_coframe,
      positiveP506MatterCurrentLorentzResponseLocalActualLift_coframe]
    exact positiveP506MatterCurrentCompleteBaseActual_coframe_one 0
  have nondegenerate :
      Matrix.det
          positiveP506MatterCurrentMatterResponseOriginField.coframe ≠ 0 := by
    rw [coframeOne]
    simp
  exact stress_apply_of_temporalSpatial03Path_hasDerivAt
    (coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField)
    (coframeMatterSectorStressCovector positiveSmoothUnifiedSource 0
      positiveP506MatterCurrentMatterResponseOriginField)
    (by
      simpa [coframeOne] using
        coframeMatterSectorLocalDensity_hasFDerivAt
          positiveSmoothUnifiedSource 0
          positiveP506MatterCurrentMatterResponseOriginField
          nondegenerate)
    (5 / 8 : ℝ)
    matterResponseOrigin_matterSectorPath_temporalSpatial03_hasDerivAt

theorem positiveP506MatterCurrentFullNonGravityCoframeStress_temporalSpatial03 :
    positiveP506MatterCurrentFullNonGravityCoframeStress
        temporalSpatial03CoframeVariation =
      (5 / 8 : ℝ) := by
  unfold positiveP506MatterCurrentFullNonGravityCoframeStress
  simp only [ContinuousLinearMap.add_apply]
  rw [matterResponseOrigin_gaugeSectorStress_temporalSpatial03,
    matterResponseOrigin_scalarSectorStress_zero,
    matterResponseOrigin_matterSectorStress_temporalSpatial03]
  norm_num


end

end
  SaturationMonoid.PhysicsCore.StageNineP506CanonicalLorentzAdjointTemporalFirstGermStress
