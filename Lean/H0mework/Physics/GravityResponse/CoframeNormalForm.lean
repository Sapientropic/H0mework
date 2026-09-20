import H0mework.Physics.GravityResponse.CoframeDefect
import H0mework.Physics.Coframe.QStarP286CoframeCoordinateClassification

/-!
# S9-C3h74a: full coframe normal form of the C3h70 defect

This module computes the full coframe lift-defect covector of the canonical
C3h70 response.  It consumes the actual C3h73 input/response fields and the
C3h61 matrix-coordinate basis.  It accepts no residual value, transport law,
zero/stationarity receipt, target coframe, or dual-to-primal identification.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseCoframeNormalForm

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorStress
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseCoframeDefect
open StageNineGravityAlgebraicKeepResponseFullDefect
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineJointShellResidualTransportRoot
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286GaugeAuxiliaryVariation
open StageNinePositiveSourceGravityMouthResidualTransportIteration
open StageNineQStarP286CoframeCoordinateClassification
open StageNineResidualLimitCoframeBalanceDecision
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitP286ScalarSourceNormalForm
open SU7MotherGaugeTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! ## Canonical one-coordinate paths -/

/-- The actual affine path through the identity in the C3h61 coordinate
direction `E_row,column`.  The case split only exposes determinant structure;
it is proved below to equal `1 + t E_row,column`. -/
def coordinateCoframe
    (row column : Fin 4) (parameter : ℝ) : LorentzianCoframe :=
  if _diagonal : row = column then
    Matrix.diagonal (fun index =>
      if index = row then 1 + parameter else 1)
  else
    Matrix.transvection row column parameter

theorem coordinateCoframe_eq_one_add
    (row column : Fin 4) (parameter : ℝ) :
    coordinateCoframe row column parameter =
      (1 : LorentzianCoframe) +
        parameter • coframeCoordinateVariation row column := by
  ext output input
  fin_cases row <;> fin_cases column <;>
    fin_cases output <;> fin_cases input <;>
    norm_num [coordinateCoframe, coframeCoordinateVariation,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.one_apply,
      Matrix.single]

@[simp] theorem coordinateCoframe_zero
    (row column : Fin 4) :
    coordinateCoframe row column 0 = (1 : LorentzianCoframe) := by
  rw [coordinateCoframe_eq_one_add]
  simp

theorem coordinateCoframe_det
    (row column : Fin 4) (parameter : ℝ) :
    Matrix.det (coordinateCoframe row column parameter) =
      if row = column then 1 + parameter else 1 := by
  by_cases diagonal : row = column
  · subst column
    fin_cases row <;>
      simp [coordinateCoframe, Matrix.det_diagonal, Fin.prod_univ_succ]
  · simp [coordinateCoframe, diagonal,
      Matrix.det_transvection_of_ne row column diagonal]

theorem coordinateCoframe_det_eventually_positive
    (row column : Fin 4) :
    ∀ᶠ parameter in nhds (0 : ℝ),
      0 < Matrix.det (coordinateCoframe row column parameter) := by
  simp_rw [coordinateCoframe_det]
  by_cases diagonal : row = column
  · filter_upwards [eventually_gt_nhds
        (show (-1 : ℝ) < 0 by norm_num)] with parameter greater
    rw [if_pos diagonal]
    linarith
  · simp [diagonal]

/-! ## Inverse-free action polynomials -/

def gravityBFPolynomial
    (coframe : LorentzianCoframe)
    (auxiliary curvature : PhysicalBivector) : ℝ :=
  gravityAuxiliaryHodgePairingPolynomial coframe auxiliary curvature -
    (1 / 2 : ℝ) *
      gravityAuxiliaryHodgePairingPolynomial coframe auxiliary
        (gravityInternalDualEquiv auxiliary)

theorem generatedGravityBFDensity_withCoframe_eq_polynomial
    (field : StageNineContinuumPointField)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    generatedGravityBFDensity (withCoframe field coframe) =
      gravityBFPolynomial coframe field.gravityAuxiliary
        field.gravityCurvature := by
  unfold generatedGravityBFDensity gravityBFPolynomial
  simp only [withCoframe]
  rw [← gravityAuxiliaryHodgePairingPolynomial_eq coframe
      nondegenerate field.gravityAuxiliary field.gravityCurvature,
    ← gravityAuxiliaryHodgePairingPolynomial_eq coframe
      nondegenerate field.gravityAuxiliary
        (gravityInternalDualEquiv field.gravityAuxiliary)]

def referenceGaugeBFPolynomial
    (coframe : LorentzianCoframe) : ℝ :=
  p286GaugeAuxiliaryHodgePairingPolynomial coframe
      referenceP286AuxiliaryCoordinate referenceP286CurvatureCoordinate +
    (1 / 4 : ℝ) *
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        referenceP286AuxiliaryCoordinate referenceP286AuxiliaryCoordinate

theorem referenceGaugeBFDensity_eq_polynomial
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    generatedGaugeSectorBFDensity p286CoordinateLiePairing coframe
        (coframeGaugeSpacetimeHodgeLinear coframe)
        ((1 / 2 : ℝ) • coframeGaugeSpacetimeHodgeLinear coframe)
        referenceP286CurvatureCoordinate referenceP286AuxiliaryCoordinate =
      referenceGaugeBFPolynomial coframe := by
  unfold generatedGaugeSectorBFDensity referenceGaugeBFPolynomial
  rw [← p286GaugeAuxiliaryHodgePairingPolynomial_eq coframe
      nondegenerate referenceP286AuxiliaryCoordinate
        referenceP286CurvatureCoordinate,
    liftGaugeTwoFormOperator_coframeHodge_constitutive_p286 coframe
      nondegenerate (1 / 2 : ℝ) referenceP286AuxiliaryCoordinate,
    generatedGaugeTwoFormMetricPairing_p286_smul_right]
  ring

theorem referenceGaugeSectorLocalDensity_eq_polynomial
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        referenceOriginField coframe =
      |Matrix.det coframe| * referenceGaugeBFPolynomial coframe := by
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
  rw [← couplingStrongWeak, ← couplingStrongHypercharge,
    ← generatedGaugeSectorBFDensity_p286_decompose,
    generatedGaugeSectorBFDensity_p286_eq_coordinate,
    positiveSource_generatedGaugeCoupling_eq_half]
  change |Matrix.det coframe| *
      generatedGaugeSectorBFDensity p286CoordinateLiePairing coframe
        (coframeGaugeSpacetimeHodgeLinear coframe)
        ((1 / 2 : ℝ) • coframeGaugeSpacetimeHodgeLinear coframe)
        referenceP286CurvatureCoordinate referenceP286AuxiliaryCoordinate = _
  rw [referenceGaugeBFDensity_eq_polynomial coframe nondegenerate]

theorem gravitySectorLocalDensity_eq_polynomial
    (field : StageNineContinuumPointField)
    (multiplierZero : field.gravitySimplicityMultiplier = 0)
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGravitySectorLocalDensity field coframe =
      |Matrix.det coframe| *
        gravityBFPolynomial coframe field.gravityAuxiliary
          field.gravityCurvature := by
  unfold coframeGravitySectorLocalDensity
  rw [generatedGravitySimplicityDensity_eq_zero_of_multiplier_eq_zero
      (withCoframe field coframe)]
  · rw [generatedGravityBFDensity_withCoframe_eq_polynomial
      field coframe nondegenerate]
    simp [generatedVolumeDensity, withCoframe]
  · exact multiplierZero

/-! ## Finite polynomial normal forms on all sixteen paths -/

def inputCombinedPolynomial (coframe : LorentzianCoframe) : ℝ :=
  gravityBFPolynomial coframe sourceGravityAuxiliaryNormalForm
      sourceGravityCurvatureNormalForm +
    referenceGaugeBFPolynomial coframe

def responseCombinedPolynomial (coframe : LorentzianCoframe) : ℝ :=
  gravityBFPolynomial coframe sourceResponseGravityAuxiliaryNormalForm
      sourceResponseGravityCurvatureNormalForm +
    referenceGaugeBFPolynomial coframe

def inputCoordinateDensityPolynomial
    (row column : Fin 4) (parameter : ℝ) : ℝ :=
  ![
    ![-(5 / 16 : ℝ) - 15 / 16 * parameter - 5 / 8 * parameter ^ 2,
      -(5 / 16 : ℝ),
      -(5 / 16 : ℝ) - 5 / 16 * parameter ^ 2,
      -(5 / 16 : ℝ) - 5 / 16 * parameter ^ 2],
    ![-(5 / 16 : ℝ),
      -(5 / 16 : ℝ) - 15 / 16 * parameter - 5 / 8 * parameter ^ 2,
      -(5 / 16 : ℝ) + 5 / 16 * parameter ^ 2,
      -(5 / 16 : ℝ) + 5 / 16 * parameter ^ 2],
    ![-(5 / 16 : ℝ), -(5 / 16 : ℝ),
      -(5 / 16 : ℝ) - 5 / 16 * parameter +
        5 / 16 * parameter ^ 2 + 5 / 16 * parameter ^ 3,
      -(5 / 16 : ℝ)],
    ![-(5 / 16 : ℝ), -(5 / 16 : ℝ), -(5 / 16 : ℝ),
      -(5 / 16 : ℝ) - 5 / 16 * parameter +
        5 / 16 * parameter ^ 2 + 5 / 16 * parameter ^ 3]
  ] row column

def responseCoordinateDensityPolynomial
    (row column : Fin 4) (parameter : ℝ) : ℝ :=
  ![
    ![-(3 / 4 : ℝ) - 29 / 16 * parameter - 17 / 16 * parameter ^ 2,
      -(3 / 4 : ℝ),
      -(3 / 4 : ℝ) - 5 / 16 * parameter ^ 2,
      -(3 / 4 : ℝ) - 5 / 16 * parameter ^ 2],
    ![-(3 / 4 : ℝ),
      -(3 / 4 : ℝ) - 29 / 16 * parameter - 17 / 16 * parameter ^ 2,
      -(3 / 4 : ℝ) + 5 / 16 * parameter ^ 2,
      -(3 / 4 : ℝ) + 5 / 16 * parameter ^ 2],
    ![-(3 / 4 : ℝ), -(3 / 4 : ℝ),
      -(3 / 4 : ℝ) - 19 / 16 * parameter -
        1 / 8 * parameter ^ 2 + 5 / 16 * parameter ^ 3,
      -(3 / 4 : ℝ)],
    ![-(3 / 4 : ℝ), -(3 / 4 : ℝ), -(3 / 4 : ℝ),
      -(3 / 4 : ℝ) - 19 / 16 * parameter -
        1 / 8 * parameter ^ 2 + 5 / 16 * parameter ^ 3]
  ] row column

@[simp] theorem p286CoordinateLiePairing_neg_left_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing (-first) second =
      -p286CoordinateLiePairing first second := by
  rw [show -first = (-1 : ℝ) • first by simp,
    p286CoordinateLiePairing_smul_left]
  ring

@[simp] theorem p286CoordinateLiePairing_neg_right_local
    (first second : P286CoordinateCarrier) :
    p286CoordinateLiePairing first (-second) =
      -p286CoordinateLiePairing first second := by
  rw [show -second = (-1 : ℝ) • second by simp,
    p286CoordinateLiePairing_smul_right]
  ring

theorem inputCombinedPolynomial_coordinate_normalForm
    (row column : Fin 4) (parameter : ℝ) :
    (if row = column then 1 + parameter else 1) *
        inputCombinedPolynomial (coordinateCoframe row column parameter) =
      inputCoordinateDensityPolynomial row column parameter := by
  fin_cases row <;> fin_cases column <;>
    simp [inputCombinedPolynomial, inputCoordinateDensityPolynomial,
      gravityBFPolynomial, referenceGaugeBFPolynomial,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual,
      gravityAuxiliaryHodgePairingPolynomial,
      p286GaugeAuxiliaryHodgePairingPolynomial,
      generatedGaugeTwoFormMetricPairing,
      coordinateCoframe, coframeTwoFormLinear, coframeWedge,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      sourceGravityAuxiliaryNormalForm, sourceGravityCurvatureNormalForm,
      referenceP286AuxiliaryCoordinate_apply,
      referenceP286CurvatureCoordinate_apply,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      canonicalP286Generator_coordinatePairing_self,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_six] <;>
    ring

private theorem responseCombinedPolynomial_coordinate_row_zero
    (column : Fin 4) (parameter : ℝ) :
    (if (0 : Fin 4) = column then 1 + parameter else 1) *
        responseCombinedPolynomial
          (coordinateCoframe 0 column parameter) =
      responseCoordinateDensityPolynomial 0 column parameter := by
  fin_cases column <;>
    simp [responseCombinedPolynomial, responseCoordinateDensityPolynomial,
      gravityBFPolynomial, referenceGaugeBFPolynomial,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual,
      gravityAuxiliaryHodgePairingPolynomial,
      p286GaugeAuxiliaryHodgePairingPolynomial,
      generatedGaugeTwoFormMetricPairing,
      coordinateCoframe, coframeTwoFormLinear, coframeWedge,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      sourceResponseGravityAuxiliaryNormalForm,
      sourceResponseGravityCurvatureNormalForm,
      referenceP286AuxiliaryCoordinate_apply,
      referenceP286CurvatureCoordinate_apply,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      canonicalP286Generator_coordinatePairing_self,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_six] <;>
    ring

private theorem responseCombinedPolynomial_coordinate_row_one
    (column : Fin 4) (parameter : ℝ) :
    (if (1 : Fin 4) = column then 1 + parameter else 1) *
        responseCombinedPolynomial
          (coordinateCoframe 1 column parameter) =
      responseCoordinateDensityPolynomial 1 column parameter := by
  fin_cases column <;>
    simp [responseCombinedPolynomial, responseCoordinateDensityPolynomial,
      gravityBFPolynomial, referenceGaugeBFPolynomial,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual,
      gravityAuxiliaryHodgePairingPolynomial,
      p286GaugeAuxiliaryHodgePairingPolynomial,
      generatedGaugeTwoFormMetricPairing,
      coordinateCoframe, coframeTwoFormLinear, coframeWedge,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      sourceResponseGravityAuxiliaryNormalForm,
      sourceResponseGravityCurvatureNormalForm,
      referenceP286AuxiliaryCoordinate_apply,
      referenceP286CurvatureCoordinate_apply,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      canonicalP286Generator_coordinatePairing_self,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_six] <;>
    ring

private theorem responseCombinedPolynomial_coordinate_row_two
    (column : Fin 4) (parameter : ℝ) :
    (if (2 : Fin 4) = column then 1 + parameter else 1) *
        responseCombinedPolynomial
          (coordinateCoframe 2 column parameter) =
      responseCoordinateDensityPolynomial 2 column parameter := by
  fin_cases column <;>
    simp [responseCombinedPolynomial, responseCoordinateDensityPolynomial,
      gravityBFPolynomial, referenceGaugeBFPolynomial,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual,
      gravityAuxiliaryHodgePairingPolynomial,
      p286GaugeAuxiliaryHodgePairingPolynomial,
      generatedGaugeTwoFormMetricPairing,
      coordinateCoframe, coframeTwoFormLinear, coframeWedge,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      sourceResponseGravityAuxiliaryNormalForm,
      sourceResponseGravityCurvatureNormalForm,
      referenceP286AuxiliaryCoordinate_apply,
      referenceP286CurvatureCoordinate_apply,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      canonicalP286Generator_coordinatePairing_self,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_six] <;>
    ring

private theorem responseCombinedPolynomial_coordinate_row_three
    (column : Fin 4) (parameter : ℝ) :
    (if (3 : Fin 4) = column then 1 + parameter else 1) *
        responseCombinedPolynomial
          (coordinateCoframe 3 column parameter) =
      responseCoordinateDensityPolynomial 3 column parameter := by
  fin_cases column <;>
    simp [responseCombinedPolynomial, responseCoordinateDensityPolynomial,
      gravityBFPolynomial, referenceGaugeBFPolynomial,
      gravityInternalDualEquiv, gravityInternalDualLinear,
      internalBivectorDual,
      gravityAuxiliaryHodgePairingPolynomial,
      p286GaugeAuxiliaryHodgePairingPolynomial,
      generatedGaugeTwoFormMetricPairing,
      coordinateCoframe, coframeTwoFormLinear, coframeWedge,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      sourceResponseGravityAuxiliaryNormalForm,
      sourceResponseGravityCurvatureNormalForm,
      referenceP286AuxiliaryCoordinate_apply,
      referenceP286CurvatureCoordinate_apply,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      canonicalP286Generator_coordinatePairing_self,
      Matrix.diagonal_apply, Matrix.transvection, Matrix.single,
      Matrix.one_apply, Fin.sum_univ_six] <;>
    ring

theorem responseCombinedPolynomial_coordinate_normalForm
    (row column : Fin 4) (parameter : ℝ) :
    (if row = column then 1 + parameter else 1) *
        responseCombinedPolynomial (coordinateCoframe row column parameter) =
      responseCoordinateDensityPolynomial row column parameter := by
  fin_cases row
  · exact responseCombinedPolynomial_coordinate_row_zero column parameter
  · exact responseCombinedPolynomial_coordinate_row_one column parameter
  · exact responseCombinedPolynomial_coordinate_row_two column parameter
  · exact responseCombinedPolynomial_coordinate_row_three column parameter

/-! ## Actual action densities on the coordinate paths -/

theorem canonicalInput_coframeLocalDensity_coordinate_normalForm
    (row column : Fin 4) (parameter : ℝ)
    (positive : 0 < Matrix.det
      (coordinateCoframe row column parameter)) :
    coframeLocalDensity positiveSmoothUnifiedSource 0 canonicalInputField
        (coordinateCoframe row column parameter) =
      inputCoordinateDensityPolynomial row column parameter := by
  rw [coframeLocalDensity_eq_sector_sum,
    gravitySectorLocalDensity_eq_polynomial canonicalInputField
      canonicalInput_multiplier_zero _ positive.ne',
    canonicalInput_gaugeSectorDensity_eq_reference,
    referenceGaugeSectorLocalDensity_eq_polynomial _ positive.ne',
    canonicalInput_scalarSectorDensity_eq_reference,
    referenceOriginField_scalarSectorLocalDensity_zero,
    canonicalInput_matterSectorDensity_zero,
    canonicalInput_gravityAuxiliary_eq_normalForm,
    canonicalInput_gravityCurvature_eq_normalForm,
    abs_of_pos positive]
  simp only [add_zero]
  rw [← mul_add, coordinateCoframe_det]
  exact inputCombinedPolynomial_coordinate_normalForm row column parameter

theorem canonicalResponse_coframeLocalDensity_coordinate_normalForm
    (row column : Fin 4) (parameter : ℝ)
    (positive : 0 < Matrix.det
      (coordinateCoframe row column parameter)) :
    coframeLocalDensity positiveSmoothUnifiedSource 0 canonicalResponseField
        (coordinateCoframe row column parameter) =
      responseCoordinateDensityPolynomial row column parameter := by
  rw [coframeLocalDensity_eq_sector_sum,
    gravitySectorLocalDensity_eq_polynomial canonicalResponseField
      canonicalResponse_multiplier_zero _ positive.ne',
    canonicalResponse_gaugeSectorDensity_eq_reference,
    referenceGaugeSectorLocalDensity_eq_polynomial _ positive.ne',
    canonicalResponse_scalarSectorDensity_eq_reference,
    referenceOriginField_scalarSectorLocalDensity_zero,
    canonicalResponse_matterSectorDensity_zero,
    canonicalResponse_gravityAuxiliary_eq_normalForm,
    canonicalResponse_gravityCurvature_eq_normalForm,
    abs_of_pos positive]
  simp only [add_zero]
  rw [← mul_add, coordinateCoframe_det]
  exact responseCombinedPolynomial_coordinate_normalForm row column parameter

/-! ## Fréchet readout of the sixteen coefficients -/

def canonicalInputCoframeCoordinateNormalForm : LorentzianCoframe :=
  Matrix.diagonal ![-(15 / 16 : ℝ), -(15 / 16 : ℝ),
    -(5 / 16 : ℝ), -(5 / 16 : ℝ)]

def canonicalResponseCoframeCoordinateNormalForm : LorentzianCoframe :=
  Matrix.diagonal ![-(29 / 16 : ℝ), -(29 / 16 : ℝ),
    -(19 / 16 : ℝ), -(19 / 16 : ℝ)]

def canonicalLiftDefectCoframeCoordinateNormalForm : LorentzianCoframe :=
  Matrix.diagonal ![-(43 / 32 : ℝ), -(43 / 32 : ℝ),
    -(33 / 32 : ℝ), -(33 / 32 : ℝ)]

def inputCoordinateDensityConstant (_row _column : Fin 4) : ℝ :=
  -(5 / 16 : ℝ)

def inputCoordinateDensityQuadratic : LorentzianCoframe :=
  ![
    ![-(5 / 8 : ℝ), 0, -(5 / 16 : ℝ), -(5 / 16 : ℝ)],
    ![0, -(5 / 8 : ℝ), 5 / 16, 5 / 16],
    ![0, 0, 5 / 16, 0],
    ![0, 0, 0, 5 / 16]
  ]

def inputCoordinateDensityCubic : LorentzianCoframe :=
  Matrix.diagonal ![(0 : ℝ), 0, 5 / 16, 5 / 16]

def responseCoordinateDensityConstant (_row _column : Fin 4) : ℝ :=
  -(3 / 4 : ℝ)

def responseCoordinateDensityQuadratic : LorentzianCoframe :=
  ![
    ![-(17 / 16 : ℝ), 0, -(5 / 16 : ℝ), -(5 / 16 : ℝ)],
    ![0, -(17 / 16 : ℝ), 5 / 16, 5 / 16],
    ![0, 0, -(1 / 8 : ℝ), 0],
    ![0, 0, 0, -(1 / 8 : ℝ)]
  ]

def responseCoordinateDensityCubic : LorentzianCoframe :=
  Matrix.diagonal ![(0 : ℝ), 0, 5 / 16, 5 / 16]

theorem inputCoordinateDensityPolynomial_eq_coefficients
    (row column : Fin 4) (parameter : ℝ) :
    inputCoordinateDensityPolynomial row column parameter =
      inputCoordinateDensityConstant row column +
        canonicalInputCoframeCoordinateNormalForm row column * parameter +
        inputCoordinateDensityQuadratic row column * parameter ^ 2 +
        inputCoordinateDensityCubic row column * parameter ^ 3 := by
  fin_cases row <;> fin_cases column <;>
    simp [inputCoordinateDensityPolynomial,
      inputCoordinateDensityConstant,
      canonicalInputCoframeCoordinateNormalForm,
      inputCoordinateDensityQuadratic, inputCoordinateDensityCubic] <;>
    ring

theorem responseCoordinateDensityPolynomial_eq_coefficients
    (row column : Fin 4) (parameter : ℝ) :
    responseCoordinateDensityPolynomial row column parameter =
      responseCoordinateDensityConstant row column +
        canonicalResponseCoframeCoordinateNormalForm row column * parameter +
        responseCoordinateDensityQuadratic row column * parameter ^ 2 +
        responseCoordinateDensityCubic row column * parameter ^ 3 := by
  fin_cases row <;> fin_cases column <;>
    simp [responseCoordinateDensityPolynomial,
      responseCoordinateDensityConstant,
      canonicalResponseCoframeCoordinateNormalForm,
      responseCoordinateDensityQuadratic, responseCoordinateDensityCubic] <;>
    ring

/-- Read the coefficient of one actual coframe-coordinate path from the
Fréchet derivative.  `formulaEventually` is a density readout, not a supplied
stress or residual certificate. -/
private theorem coframeStress_coordinate_of_eventually_cubic
    (field : StageNineContinuumPointField)
    (coframeOne : field.coframe = (1 : LorentzianCoframe))
    (row column : Fin 4)
    (constant linear quadratic cubic : ℝ)
    (formulaEventually : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun parameter : ℝ =>
        coframeLocalDensity positiveSmoothUnifiedSource 0 field
          ((1 : LorentzianCoframe) +
            parameter • coframeCoordinateVariation row column))
      (fun parameter : ℝ =>
        constant + linear * parameter + quadratic * parameter ^ 2 +
          cubic * parameter ^ 3)) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0 field
        (coframeCoordinateVariation row column) = linear := by
  have nondegenerate : Matrix.det field.coframe ≠ 0 := by
    rw [coframeOne]
    simp
  have outer := coframeLocalDensity_hasFDerivAt
    positiveSmoothUnifiedSource 0 field nondegenerate
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have coordinateDerivative := identityDerivative.smul_const
    (coframeCoordinateVariation row column)
  have coordinateDerivativeValue :
      (1 : ℝ) • coframeCoordinateVariation row column =
        coframeCoordinateVariation row column := by
    simp
  have coordinateDerivativeAtZero :=
    coordinateDerivative.congr_deriv coordinateDerivativeValue
  have pathDerivative := coordinateDerivativeAtZero.const_add
    (1 : LorentzianCoframe)
  have pointEquality :
      field.coframe =
        (1 : LorentzianCoframe) +
          (0 : ℝ) • coframeCoordinateVariation row column := by
    rw [coframeOne]
    simp
  have composed := outer.comp_hasDerivAt_of_eq (0 : ℝ)
    pathDerivative pointEquality
  have polynomial :=
    (((hasDerivAt_const (x := (0 : ℝ)) constant).add
      (identityDerivative.const_mul linear)).add
      ((identityDerivative.pow 2).const_mul quadratic)).add
      ((identityDerivative.pow 3).const_mul cubic)
  have exactDerivative := polynomial.congr_of_eventuallyEq formulaEventually
  have derivativeEquality := composed.unique exactDerivative
  norm_num at derivativeEquality
  exact derivativeEquality

theorem canonicalInput_coframeStress_coordinate_normalForm
    (row column : Fin 4) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        canonicalInputField (coframeCoordinateVariation row column) =
      canonicalInputCoframeCoordinateNormalForm row column := by
  apply coframeStress_coordinate_of_eventually_cubic canonicalInputField
    canonicalInput_coframe_eq_one row column
    (inputCoordinateDensityConstant row column)
    (canonicalInputCoframeCoordinateNormalForm row column)
    (inputCoordinateDensityQuadratic row column)
    (inputCoordinateDensityCubic row column)
  filter_upwards [coordinateCoframe_det_eventually_positive row column]
      with parameter positive
  rw [← coordinateCoframe_eq_one_add row column parameter,
    canonicalInput_coframeLocalDensity_coordinate_normalForm
      row column parameter positive,
    inputCoordinateDensityPolynomial_eq_coefficients]

theorem canonicalResponse_coframeStress_coordinate_normalForm
    (row column : Fin 4) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        canonicalResponseField (coframeCoordinateVariation row column) =
      canonicalResponseCoframeCoordinateNormalForm row column := by
  apply coframeStress_coordinate_of_eventually_cubic canonicalResponseField
    canonicalResponse_coframe_eq_one row column
    (responseCoordinateDensityConstant row column)
    (canonicalResponseCoframeCoordinateNormalForm row column)
    (responseCoordinateDensityQuadratic row column)
    (responseCoordinateDensityCubic row column)
  filter_upwards [coordinateCoframe_det_eventually_positive row column]
      with parameter positive
  rw [← coordinateCoframe_eq_one_add row column parameter,
    canonicalResponse_coframeLocalDensity_coordinate_normalForm
      row column parameter positive,
    responseCoordinateDensityPolynomial_eq_coefficients]

/-! ## The actual C3h70 lift defect -/

theorem canonicalResponseCoframeActualDelta_coordinate_normalForm
    (row column : Fin 4) :
    algebraicKeepResponseCoframeActualDelta
        residualLimitLorentzCarrierReader
        (coframeCoordinateVariation row column) =
      canonicalResponseCoframeCoordinateNormalForm row column -
        canonicalInputCoframeCoordinateNormalForm row column := by
  change
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
          canonicalResponseField (coframeCoordinateVariation row column) -
        coframeLocalStressCovector positiveSmoothUnifiedSource 0
          canonicalInputField (coframeCoordinateVariation row column) = _
  rw [canonicalResponse_coframeStress_coordinate_normalForm,
    canonicalInput_coframeStress_coordinate_normalForm]

theorem canonicalInputTrace_coframe_coordinate_normalForm
    (row column : Fin 4) :
    (algebraicKeepResponseInputTrace
        residualLimitLorentzCarrierReader).eulerLagrange.coframe
        (coframeCoordinateVariation row column) =
      (1 / 2 : ℝ) *
        canonicalInputCoframeCoordinateNormalForm row column := by
  unfold algebraicKeepResponseInputTrace currentJointShellResidualTrace
    currentJointShellResidualKeep linearResidualTrace scalarKeepLinearMap
  rw [positiveSmoothUnifiedSource_legacy_sigma_eq_half]
  change
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
          canonicalInputField (coframeCoordinateVariation row column) -
        (1 - (1 / 2 : ℝ)) *
          coframeLocalStressCovector positiveSmoothUnifiedSource 0
            canonicalInputField (coframeCoordinateVariation row column) = _
  rw [canonicalInput_coframeStress_coordinate_normalForm]
  ring

theorem canonicalLiftDefectCoframeCoordinateNormalForm_eq_response_sub_half_input :
    canonicalLiftDefectCoframeCoordinateNormalForm =
      canonicalResponseCoframeCoordinateNormalForm -
        (1 / 2 : ℝ) • canonicalInputCoframeCoordinateNormalForm := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [canonicalLiftDefectCoframeCoordinateNormalForm,
      canonicalResponseCoframeCoordinateNormalForm,
      canonicalInputCoframeCoordinateNormalForm, Matrix.diagonal_apply]

theorem canonicalLiftDefect_coframe_coordinate_normalForm
    (row column : Fin 4) :
    (algebraicKeepResponseLiftDefect
        residualLimitLorentzCarrierReader).eulerLagrange.coframe
        (coframeCoordinateVariation row column) =
      canonicalLiftDefectCoframeCoordinateNormalForm row column := by
  have split := congrArg
    (fun covector : LorentzianCoframe →L[ℝ] ℝ =>
      covector (coframeCoordinateVariation row column))
    (algebraicKeepResponseLiftDefect_coframe_eq_actualDelta_add_trace
      residualLimitLorentzCarrierReader)
  change
    (algebraicKeepResponseLiftDefect
        residualLimitLorentzCarrierReader).eulerLagrange.coframe
          (coframeCoordinateVariation row column) =
      algebraicKeepResponseCoframeActualDelta
          residualLimitLorentzCarrierReader
          (coframeCoordinateVariation row column) +
        (algebraicKeepResponseInputTrace
          residualLimitLorentzCarrierReader).eulerLagrange.coframe
          (coframeCoordinateVariation row column) at split
  rw [canonicalResponseCoframeActualDelta_coordinate_normalForm,
    canonicalInputTrace_coframe_coordinate_normalForm] at split
  calc
    (algebraicKeepResponseLiftDefect
        residualLimitLorentzCarrierReader).eulerLagrange.coframe
          (coframeCoordinateVariation row column) =
        (canonicalResponseCoframeCoordinateNormalForm row column -
            canonicalInputCoframeCoordinateNormalForm row column) +
          (1 / 2 : ℝ) *
            canonicalInputCoframeCoordinateNormalForm row column := split
    _ = canonicalLiftDefectCoframeCoordinateNormalForm row column := by
      fin_cases row <;> fin_cases column <;>
        norm_num [canonicalLiftDefectCoframeCoordinateNormalForm,
          canonicalResponseCoframeCoordinateNormalForm,
          canonicalInputCoframeCoordinateNormalForm, Matrix.diagonal_apply]

/-! ## Support, the `2 + 2` split, and the radial boundary -/

theorem canonicalLiftDefect_coframe_coordinate_zero_of_ne
    (row column : Fin 4) (offDiagonal : row ≠ column) :
    (algebraicKeepResponseLiftDefect
        residualLimitLorentzCarrierReader).eulerLagrange.coframe
        (coframeCoordinateVariation row column) = 0 := by
  rw [canonicalLiftDefect_coframe_coordinate_normalForm]
  simp [canonicalLiftDefectCoframeCoordinateNormalForm,
    offDiagonal]

theorem canonicalLiftDefectCoframeCoordinateNormalForm_two_plus_two :
    canonicalLiftDefectCoframeCoordinateNormalForm 0 0 =
        canonicalLiftDefectCoframeCoordinateNormalForm 1 1 ∧
      canonicalLiftDefectCoframeCoordinateNormalForm 2 2 =
        canonicalLiftDefectCoframeCoordinateNormalForm 3 3 ∧
      canonicalLiftDefectCoframeCoordinateNormalForm 0 0 ≠
        canonicalLiftDefectCoframeCoordinateNormalForm 2 2 := by
  constructor
  · change (-(43 / 32 : ℝ)) = -(43 / 32 : ℝ)
    rfl
  constructor
  · change (-(33 / 32 : ℝ)) = -(33 / 32 : ℝ)
    rfl
  · change (-(43 / 32 : ℝ)) ≠ -(33 / 32 : ℝ)
    norm_num

theorem canonicalLiftDefectCoframeCoordinateNormalForm_diagonal_sum :
    (∑ index : Fin 4,
      canonicalLiftDefectCoframeCoordinateNormalForm index index) =
        -(19 / 4 : ℝ) := by
  rw [Fin.sum_univ_four]
  change
    (-(43 / 32 : ℝ)) + -(43 / 32 : ℝ) +
      -(33 / 32 : ℝ) + -(33 / 32 : ℝ) = -(19 / 4 : ℝ)
  norm_num

/-- Canonical-coordinate criterion for a scalar-identity dual: its values on
the declared matrix basis are one common scalar on the diagonal and zero off
the diagonal. -/
def IsScalarIdentityCoordinateDual
    (covector : LorentzianCoframe →L[ℝ] ℝ) : Prop :=
  ∃ scalar : ℝ, ∀ row column : Fin 4,
    covector (coframeCoordinateVariation row column) =
      scalar * (1 : LorentzianCoframe) row column

/-- The full defect is block symmetric but not a pure radial/scalar-identity
dual.  This is only a negative carrier boundary; it does not identify the
covector with a coframe state. -/
theorem canonicalLiftDefect_coframe_not_scalarIdentityCoordinateDual :
    ¬ IsScalarIdentityCoordinateDual
      (algebraicKeepResponseLiftDefect
        residualLimitLorentzCarrierReader).eulerLagrange.coframe := by
  rintro ⟨scalar, coordinateValue⟩
  have timeValue := coordinateValue 0 0
  have spatialValue := coordinateValue 2 2
  rw [canonicalLiftDefect_coframe_coordinate_normalForm] at timeValue spatialValue
  change (-(43 / 32 : ℝ)) = scalar * 1 at timeValue
  change (-(33 / 32 : ℝ)) = scalar * 1 at spatialValue
  norm_num at timeValue spatialValue
  linarith

end

end SaturationMonoid.PhysicsCore.StageNineGravityAlgebraicKeepResponseCoframeNormalForm
