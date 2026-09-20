import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import H0mework.Physics.GaugeAction.FixedCurvatureP286CanonicalAuxiliary
import H0mework.Physics.GravityResponse.CoframeNormalForm

/-!
# Stage-9 biradial coframe response

This module derives the existing-field biradial point carrier and proves that
its complete sixteen-coordinate coframe stress reaches the half-kept reference
stress at one unique positive parameter pair.  The parameters are classified
from the actual action density; no numerical root, branch receipt, target
state, new field, coupling, or source slot is supplied.

It is an internal inhabitability component for the complete synchronized
nine-channel response.  It is not by itself a physical update producer.
-/

namespace SaturationMonoid.PhysicsCore.StageNineBiradialCoframeResponse

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeLocalDifferentiability
open StageNineCoframeSectorStress
open StageNineEnrichedProofFreeSource
open StageNineFixedCurvatureP286CanonicalAuxiliary
open StageNineGlobalIntegratedAction
open StageNineGravityAlgebraicKeepResponseCoframeNormalForm
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeAuxiliaryEquation
open StageNineQStarP286CoframeCoordinateClassification
open StageNineResidualLimitCoframeBalanceDecision
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set

def biradialBalanceA (b : ℝ) : ℝ :=
  192 * b ^ 4 + 30

def biradialBalanceC (b : ℝ) : ℝ :=
  192 * b ^ 4 + 10

def biradialBalanceRatio (b : ℝ) : ℝ :=
  b ^ 7 * biradialBalanceA b ^ 6 /
    biradialBalanceC b ^ 5

def biradialBalanceTarget : ℝ :=
  111 ^ 6 / 101 ^ 5

def biradialAOfB (b : ℝ) : ℝ :=
  (101 / 111 : ℝ) * b *
    biradialBalanceA b / biradialBalanceC b

def BiradialBalance (a b : ℝ) : Prop :=
  a ^ 5 * b ^ 2 * biradialBalanceA b = 111 ∧
    a ^ 6 * b * biradialBalanceC b = 101

def biradialDerivativeNumerator (t : ℝ) : ℝ :=
  405504 * t ^ 2 - 15360 * t + 2100

private theorem pow_four_hasDerivAt (b : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 4) (4 * b ^ 3) b := by
  convert! (hasDerivAt_id b).pow 4 using 1
  all_goals norm_num

theorem biradialBalanceA_hasDerivAt (b : ℝ) :
    HasDerivAt biradialBalanceA (768 * b ^ 3) b := by
  unfold biradialBalanceA
  convert! (((pow_four_hasDerivAt b).const_mul 192).add
    (hasDerivAt_const (x := b) (30 : ℝ))) using 1
  all_goals ring

theorem biradialBalanceC_hasDerivAt (b : ℝ) :
    HasDerivAt biradialBalanceC (768 * b ^ 3) b := by
  unfold biradialBalanceC
  convert! (((pow_four_hasDerivAt b).const_mul 192).add
    (hasDerivAt_const (x := b) (10 : ℝ))) using 1
  all_goals ring

theorem biradialBalanceA_pos (b : ℝ) :
    0 < biradialBalanceA b := by
  unfold biradialBalanceA
  positivity

theorem biradialBalanceC_pos (b : ℝ) :
    0 < biradialBalanceC b := by
  unfold biradialBalanceC
  positivity

theorem biradialDerivativeNumerator_pos (t : ℝ) :
    0 < biradialDerivativeNumerator t := by
  unfold biradialDerivativeNumerator
  nlinarith [sq_nonneg (67584 * t - 1280)]

theorem biradialBalanceRatio_hasDerivAt (b : ℝ) :
    HasDerivAt biradialBalanceRatio
      (b ^ 6 * biradialBalanceA b ^ 5 /
          biradialBalanceC b ^ 6 *
        biradialDerivativeNumerator (b ^ 4)) b := by
  have numerator :=
    ((hasDerivAt_id b).pow 7).mul
      ((biradialBalanceA_hasDerivAt b).pow 6)
  have denominator :=
    (biradialBalanceC_hasDerivAt b).pow 5
  have quotient :=
    numerator.div denominator
      (pow_ne_zero 5 (biradialBalanceC_pos b).ne')
  convert! quotient using 1
  simp only [Pi.pow_apply, Pi.mul_apply, id_eq]
  unfold biradialBalanceA biradialBalanceC
    biradialDerivativeNumerator
  field_simp
  ring

theorem biradialBalanceRatio_continuous :
    Continuous biradialBalanceRatio := by
  unfold biradialBalanceRatio biradialBalanceA biradialBalanceC
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro b
    exact pow_ne_zero 5 (biradialBalanceC_pos b).ne'

theorem biradialBalanceRatio_strictMonoOn :
    StrictMonoOn biradialBalanceRatio (Ioi 0) := by
  let derivative := fun b : ℝ =>
    b ^ 6 * biradialBalanceA b ^ 5 /
        biradialBalanceC b ^ 6 *
      biradialDerivativeNumerator (b ^ 4)
  refine strictMonoOn_of_hasDerivWithinAt_pos
    (f' := derivative)
    (convex_Ioi 0)
    biradialBalanceRatio_continuous.continuousOn
    ?_ ?_
  · intro b _hb
    exact
      (biradialBalanceRatio_hasDerivAt b).hasDerivWithinAt
  · intro b hb
    rw [interior_Ioi] at hb
    dsimp only [derivative]
    have hb6 : 0 < b ^ 6 := pow_pos hb 6
    have hA5 : 0 < biradialBalanceA b ^ 5 :=
      pow_pos (biradialBalanceA_pos b) 5
    have hC6 : 0 < biradialBalanceC b ^ 6 :=
      pow_pos (biradialBalanceC_pos b) 6
    have hN :
        0 < biradialDerivativeNumerator (b ^ 4) :=
      biradialDerivativeNumerator_pos _
    positivity

theorem existsUnique_positive_biradialBalanceRatio :
    ∃! b : ℝ,
      0 < b ∧
        biradialBalanceRatio b = biradialBalanceTarget := by
  have lower :
      biradialBalanceRatio (9 / 10 : ℝ) <
        biradialBalanceTarget := by
    norm_num [
      biradialBalanceRatio,
      biradialBalanceTarget,
      biradialBalanceA,
      biradialBalanceC
    ]
  have upper :
      biradialBalanceTarget <
        biradialBalanceRatio 1 := by
    norm_num [
      biradialBalanceRatio,
      biradialBalanceTarget,
      biradialBalanceA,
      biradialBalanceC
    ]
  have between :
      biradialBalanceTarget ∈
        Icc
          (biradialBalanceRatio (9 / 10 : ℝ))
          (biradialBalanceRatio 1) :=
    ⟨lower.le, upper.le⟩
  obtain ⟨b, hb, value⟩ :=
    intermediate_value_Icc
      (a := (9 / 10 : ℝ)) (b := 1)
      (by norm_num)
      biradialBalanceRatio_continuous.continuousOn
      between
  have positive : 0 < b := by
    nlinarith [hb.1]
  refine ⟨b, ⟨positive, value⟩, ?_⟩
  intro candidate candidateProperty
  exact biradialBalanceRatio_strictMonoOn.injOn
    candidateProperty.1 positive
    (candidateProperty.2.trans value.symm)

theorem biradialBalance_iff (a b : ℝ) :
    BiradialBalance a b ↔
      a = biradialAOfB b ∧
        biradialBalanceRatio b = biradialBalanceTarget := by
  constructor
  · rintro ⟨first, second⟩
    have cross :
        111 * a * biradialBalanceC b =
          101 * b * biradialBalanceA b := by
      rw [← first, ← second]
      ring
    have a_eq : a = biradialAOfB b := by
      unfold biradialAOfB
      field_simp [(biradialBalanceC_pos b).ne']
      linarith
    refine ⟨a_eq, ?_⟩
    rw [a_eq] at first
    unfold biradialAOfB at first
    unfold biradialBalanceRatio biradialBalanceTarget
    field_simp [(biradialBalanceC_pos b).ne'] at first ⊢
    nlinarith
  · rintro ⟨a_eq, ratio_eq⟩
    rw [a_eq]
    unfold biradialBalanceRatio biradialBalanceTarget at ratio_eq
    unfold biradialAOfB BiradialBalance
    field_simp [(biradialBalanceC_pos b).ne'] at ratio_eq ⊢
    constructor <;> nlinarith

theorem biradialAOfB_pos {b : ℝ} (hb : 0 < b) :
    0 < biradialAOfB b := by
  unfold biradialAOfB
  have hA := biradialBalanceA_pos b
  have hC := biradialBalanceC_pos b
  positivity

theorem existsUnique_positive_biradialBalance :
    ∃! p : ℝ × ℝ,
      0 < p.1 ∧
        0 < p.2 ∧
          BiradialBalance p.1 p.2 := by
  rcases existsUnique_positive_biradialBalanceRatio with
    ⟨b, hb, uniqueB⟩
  let a := biradialAOfB b
  have ha : 0 < a := biradialAOfB_pos hb.1
  have balance : BiradialBalance a b :=
    (biradialBalance_iff a b).2 ⟨rfl, hb.2⟩
  refine ⟨(a, b), ⟨ha, hb.1, balance⟩, ?_⟩
  rintro ⟨candidateA, candidateB⟩
    ⟨_, candidateBPositive, candidateBalance⟩
  have characterization :=
    (biradialBalance_iff candidateA candidateB).1
      candidateBalance
  have candidateB_eq : candidateB = b :=
    uniqueB candidateB
      ⟨candidateBPositive, characterization.2⟩
  apply Prod.ext
  · change candidateA = a
    rw [characterization.1, candidateB_eq]
  · exact candidateB_eq

theorem biradialBalance_iff_expanded (a b : ℝ) :
    BiradialBalance a b ↔
      192 * a ^ 5 * b ^ 6 +
            30 * a ^ 5 * b ^ 2 = 111 ∧
        192 * a ^ 6 * b ^ 5 +
            10 * a ^ 6 * b = 101 := by
  unfold BiradialBalance biradialBalanceA biradialBalanceC
  constructor <;> rintro ⟨h₁, h₂⟩ <;>
    constructor <;> nlinarith

/-! ## Existing-field point carrier used by the full response probe -/

def biradialCoframe (a b : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![a, a, b, b]

theorem biradialCoframe_det (a b : ℝ) :
    Matrix.det (biradialCoframe a b) = a ^ 2 * b ^ 2 := by
  simp [biradialCoframe, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

def biradialCoframeDetCoordinateSlope
    (a b : ℝ) : Fin 4 → ℝ :=
  ![a * b ^ 2, a * b ^ 2, a ^ 2 * b, a ^ 2 * b]

private theorem biradialCoframe_diagonalCoordinate_eq_updateRow
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (row : Fin 4) (parameter : ℝ) :
    biradialCoframe a b +
        parameter • coframeCoordinateVariation row row =
      Matrix.updateRow (biradialCoframe a b) row
        ((1 + parameter / biradialCoframe a b row row) •
          biradialCoframe a b row) := by
  ext output input
  fin_cases row <;> fin_cases output <;> fin_cases input <;>
    simp [biradialCoframe, coframeCoordinateVariation,
      Matrix.updateRow_apply]
  all_goals field_simp [ha, hb]

private theorem biradialCoframe_offDiagonalCoordinate_eq_transvection
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {row column : Fin 4} (offDiagonal : row ≠ column)
    (parameter : ℝ) :
    biradialCoframe a b +
        parameter • coframeCoordinateVariation row column =
      biradialCoframe a b * Matrix.transvection row column
        (parameter / biradialCoframe a b row row) := by
  ext output input
  fin_cases row <;> fin_cases column <;>
    fin_cases output <;> fin_cases input <;>
    simp [biradialCoframe, coframeCoordinateVariation,
      Matrix.transvection, Matrix.mul_apply, Matrix.diagonal_apply]
      at offDiagonal ⊢
  all_goals field_simp [ha, hb]

theorem biradialCoframe_coordinate_det
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (row column : Fin 4) (parameter : ℝ) :
    Matrix.det
        (biradialCoframe a b +
          parameter • coframeCoordinateVariation row column) =
      a ^ 2 * b ^ 2 +
        if row = column then
          biradialCoframeDetCoordinateSlope a b row * parameter
        else 0 := by
  by_cases diagonal : row = column
  · subst column
    rw [if_pos rfl,
      biradialCoframe_diagonalCoordinate_eq_updateRow ha hb,
      Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
      biradialCoframe_det]
    fin_cases row <;>
      simp [biradialCoframe, biradialCoframeDetCoordinateSlope] <;>
      field_simp [ha, hb]
  · rw [if_neg diagonal, add_zero,
      biradialCoframe_offDiagonalCoordinate_eq_transvection
        ha hb diagonal,
      Matrix.det_mul,
      Matrix.det_transvection_of_ne row column diagonal,
      biradialCoframe_det, mul_one]

theorem biradialCoframe_one_one :
    biradialCoframe 1 1 = (1 : LorentzianCoframe) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [biradialCoframe]

theorem biradialCoframe_inv
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (biradialCoframe a b)⁻¹ =
      biradialCoframe a⁻¹ b⁻¹ := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [biradialCoframe, Matrix.mul_apply, Matrix.diagonal_apply, ha, hb]

theorem coframeTwoFormLinear_biradial
    (a b : ℝ) (form : GaugeTwoForm) :
    coframeTwoFormLinear (biradialCoframe a b) form =
      ![a ^ 2 * form 0, a * b * form 1, a * b * form 2,
        b ^ 2 * form 3, a * b * form 4, a * b * form 5] := by
  funext pair
  fin_cases pair <;>
    simp [coframeTwoFormLinear, biradialCoframe, coframeWedge,
      pairFirst, pairSecond, Matrix.diagonal_apply, Fin.sum_univ_six] <;>
    ring_nf <;> simp

theorem biradialCoframe_spacetimeHodge_apply
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (form : GaugeTwoForm) :
    coframeGaugeSpacetimeHodgeLinear (biradialCoframe a b) form =
      ![(b ^ 2 / a ^ 2) * form 3, form 4, form 5,
        -(a ^ 2 / b ^ 2) * form 0, -form 1, -form 2] := by
  unfold coframeGaugeSpacetimeHodgeLinear inverseCoframeTwoFormLinear
  rw [biradialCoframe_inv ha hb]
  change coframeTwoFormLinear (biradialCoframe a⁻¹ b⁻¹)
      (lorentzianCoframeHodge
        (coframeTwoFormLinear (biradialCoframe a b) form)) = _
  rw [coframeTwoFormLinear_biradial, coframeTwoFormLinear_biradial]
  ext pair
  fin_cases pair <;>
    simp [lorentzianCoframeHodge] <;>
    field_simp [ha, hb]

theorem liftGaugeTwoFormOperator_biradialHodge
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (form : Fin 6 → V) :
    liftGaugeTwoFormOperator
        (coframeGaugeSpacetimeHodgeLinear (biradialCoframe a b)) form =
      ![(b ^ 2 / a ^ 2) • form 3, form 4, form 5,
        -(a ^ 2 / b ^ 2) • form 0, -form 1, -form 2] := by
  funext output
  fin_cases output <;>
    simp [liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      biradialCoframe_spacetimeHodge_apply ha hb]

def fixedCurvatureBiradialPointField (a b : ℝ) :
    StageNineContinuumPointField :=
  let coframe := biradialCoframe a b
  let gravityAuxiliary := physicalIIPlusBivector coframe
  { referenceOriginField with
    coframe := coframe
    gravityAuxiliary := gravityAuxiliary
    gravityCurvature := gravityInternalDualEquiv gravityAuxiliary
    gaugeCurvature := referenceOriginField.gaugeCurvature
    gaugeAuxiliary :=
      generatedP286GaugeConstitutiveAuxiliary
        positiveSmoothUnifiedSource coframe
        referenceOriginField.gaugeCurvature }

theorem fixedCurvatureBiradialPointField_simplicity
    (a b : ℝ) :
    (fixedCurvatureBiradialPointField a b).gravityAuxiliary =
      physicalIIPlusBivector
        (fixedCurvatureBiradialPointField a b).coframe :=
  rfl

theorem fixedCurvatureBiradialPointField_gravityConstitutive
    (a b : ℝ) :
    (fixedCurvatureBiradialPointField a b).gravityCurvature =
      gravityInternalDualEquiv
        (fixedCurvatureBiradialPointField a b).gravityAuxiliary :=
  rfl

theorem fixedCurvatureBiradialPointField_p286Constitutive
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (fixedCurvatureBiradialPointField a b).coframe)
        (fixedCurvatureBiradialPointField a b).gaugeAuxiliary =
      (fixedCurvatureBiradialPointField a b).gaugeCurvature := by
  apply generatedP286GaugeConstitutiveAuxiliary_solves
  change Matrix.det (biradialCoframe a b) ≠ 0
  rw [biradialCoframe_det]
  exact mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)

def biradialP286AuxiliaryCoordinate (a b : ℝ) : P286GaugeTwoForm :=
  fun pair =>
    p286CoordinateEquiv
      ((fixedCurvatureBiradialPointField a b).gaugeAuxiliary pair)

theorem biradialP286AuxiliaryCoordinate_apply
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (pair : Fin 6) :
    biradialP286AuxiliaryCoordinate a b pair =
      if pair = 3 then
        (a ^ 2 / (2 * b ^ 2)) •
          p286CoordinateEquiv canonicalP286Generator
      else 0 := by
  unfold biradialP286AuxiliaryCoordinate
    fixedCurvatureBiradialPointField
    generatedP286GaugeConstitutiveAuxiliary
  simp only [p286CoordinateEquiv.apply_symm_apply]
  change
    p286GaugeConstitutiveAuxiliaryCoordinate positiveSmoothUnifiedSource
        (biradialCoframe a b) referenceP286CurvatureCoordinate pair = _
  unfold p286GaugeConstitutiveAuxiliaryCoordinate
  rw [positiveSource_generatedGaugeCoupling_eq_half,
    liftGaugeTwoFormOperator_biradialHodge ha hb]
  simp_rw [referenceP286CurvatureCoordinate_apply]
  fin_cases pair
  all_goals simp [smul_smul]
  all_goals field_simp [ha, hb]
  all_goals ring_nf

theorem fixedCurvatureBiradialPointField_one_one :
    fixedCurvatureBiradialPointField 1 1 = referenceOriginField := by
  apply StageNineContinuumPointField.ext
  · change biradialCoframe 1 1 = referenceOriginField.coframe
    rw [biradialCoframe_one_one, referenceOriginField_coframe_eq_one]
  · change
      gravityInternalDualEquiv
          (physicalIIPlusBivector (biradialCoframe 1 1)) =
        referenceOriginField.gravityCurvature
    rw [biradialCoframe_one_one]
    exact
      (congrArg gravityInternalDualEquiv
        referenceOriginField_gravityAuxiliary_eq_physical.symm).trans
      referenceOriginField_gravityCurvature_eq_constitutive.symm
  · change physicalIIPlusBivector (biradialCoframe 1 1) =
      referenceOriginField.gravityAuxiliary
    rw [biradialCoframe_one_one]
    exact referenceOriginField_gravityAuxiliary_eq_physical.symm
  · rfl
  · rfl
  · change
      generatedP286GaugeConstitutiveAuxiliary
          positiveSmoothUnifiedSource (biradialCoframe 1 1)
          referenceOriginField.gaugeCurvature =
        referenceOriginField.gaugeAuxiliary
    rw [biradialCoframe_one_one]
    exact
      generatedP286GaugeConstitutiveAuxiliary_identity_eq_reference
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Inverse-free density used to read the complete coframe covector -/

def biradialGaugeBFPolynomial
    (a b : ℝ) (coframe : LorentzianCoframe) : ℝ :=
  p286GaugeAuxiliaryHodgePairingPolynomial coframe
      (biradialP286AuxiliaryCoordinate a b)
      referenceP286CurvatureCoordinate +
    (1 / 4 : ℝ) *
      generatedGaugeTwoFormMetricPairing p286CoordinateLiePairing coframe
        (biradialP286AuxiliaryCoordinate a b)
        (biradialP286AuxiliaryCoordinate a b)

theorem fixedCurvatureBiradial_gaugeSectorLocalDensity_eq_polynomial
    {a b : ℝ}
    (coframe : LorentzianCoframe)
    (nondegenerate : Matrix.det coframe ≠ 0) :
    coframeGaugeSectorLocalDensity positiveSmoothUnifiedSource
        (fixedCurvatureBiradialPointField a b) coframe =
      |Matrix.det coframe| * biradialGaugeBFPolynomial a b coframe := by
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
        referenceP286CurvatureCoordinate
        (biradialP286AuxiliaryCoordinate a b) =
      |Matrix.det coframe| * biradialGaugeBFPolynomial a b coframe
  congr 1
  unfold generatedGaugeSectorBFDensity biradialGaugeBFPolynomial
  rw [← p286GaugeAuxiliaryHodgePairingPolynomial_eq coframe
      nondegenerate (biradialP286AuxiliaryCoordinate a b)
      referenceP286CurvatureCoordinate,
    liftGaugeTwoFormOperator_coframeHodge_constitutive_p286 coframe
      nondegenerate (1 / 2 : ℝ)
      (biradialP286AuxiliaryCoordinate a b),
    generatedGaugeTwoFormMetricPairing_p286_smul_right]
  ring

theorem fixedCurvatureBiradial_scalarSectorLocalDensity_zero
    (a b : ℝ) (coframe : LorentzianCoframe) :
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
        (fixedCurvatureBiradialPointField a b) coframe = 0 := by
  change
    coframeScalarSectorLocalDensity positiveSmoothUnifiedSource 0
      referenceOriginField coframe = 0
  exact referenceOriginField_scalarSectorLocalDensity_zero coframe

theorem fixedCurvatureBiradial_matterSectorLocalDensity_zero
    (a b : ℝ) (coframe : LorentzianCoframe) :
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
        (fixedCurvatureBiradialPointField a b) coframe = 0 := by
  change
    coframeMatterSectorLocalDensity positiveSmoothUnifiedSource 0
      referenceOriginField coframe = 0
  exact referenceOriginField_matterSectorLocalDensity_zero coframe

def biradialTotalDensityPolynomial
    (a b : ℝ) (coframe : LorentzianCoframe) : ℝ :=
  Matrix.det coframe *
    (gravityBFPolynomial coframe
        (fixedCurvatureBiradialPointField a b).gravityAuxiliary
        (fixedCurvatureBiradialPointField a b).gravityCurvature +
      biradialGaugeBFPolynomial a b coframe)

theorem fixedCurvatureBiradial_localDensity_eq_polynomial
    {a b : ℝ}
    (coframe : LorentzianCoframe)
    (positive : 0 < Matrix.det coframe) :
    coframeLocalDensity positiveSmoothUnifiedSource 0
        (fixedCurvatureBiradialPointField a b) coframe =
      biradialTotalDensityPolynomial a b coframe := by
  rw [coframeLocalDensity_eq_sector_sum,
    gravitySectorLocalDensity_eq_polynomial
      (fixedCurvatureBiradialPointField a b) rfl coframe positive.ne',
    fixedCurvatureBiradial_gaugeSectorLocalDensity_eq_polynomial
      coframe positive.ne',
    fixedCurvatureBiradial_scalarSectorLocalDensity_zero,
    fixedCurvatureBiradial_matterSectorLocalDensity_zero,
    abs_of_pos positive]
  unfold biradialTotalDensityPolynomial
  ring

def biradialCoframeStressNormalForm
    (a b : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![
    -6 * a ^ 5 * b ^ 6 - 15 / 16 * a ^ 5 * b ^ 2,
    -6 * a ^ 5 * b ^ 6 - 15 / 16 * a ^ 5 * b ^ 2,
    -6 * a ^ 6 * b ^ 5 - 5 / 16 * a ^ 6 * b,
    -6 * a ^ 6 * b ^ 5 - 5 / 16 * a ^ 6 * b]

def biradialTotalDensityConstant (a b : ℝ) : ℝ :=
  -3 * a ^ 6 * b ^ 6 - 5 / 16 * a ^ 6 * b ^ 2

def biradialTotalDensityQuadraticNormalForm
    (a b : ℝ) : LorentzianCoframe :=
  ![
    ![-3 * a ^ 4 * b ^ 6 - 5 / 8 * a ^ 4 * b ^ 2,
      0, -5 / 16 * a ^ 6, -5 / 16 * a ^ 6],
    ![0, -3 * a ^ 4 * b ^ 6 - 5 / 8 * a ^ 4 * b ^ 2,
      5 / 16 * a ^ 6, 5 / 16 * a ^ 6],
    ![0, 0, -3 * a ^ 6 * b ^ 4 + 5 / 16 * a ^ 6, 0],
    ![0, 0, 0, -3 * a ^ 6 * b ^ 4 + 5 / 16 * a ^ 6]
  ]

def biradialTotalDensityCubicNormalForm
    (a b : ℝ) : LorentzianCoframe :=
  Matrix.diagonal ![
    (0 : ℝ), 0,
    5 / 16 * a ^ 6 / b,
    5 / 16 * a ^ 6 / b]

def biradialCoordinateDensityPolynomial
    (a b : ℝ) (row column : Fin 4) (parameter : ℝ) : ℝ :=
  biradialTotalDensityConstant a b +
    biradialCoframeStressNormalForm a b row column * parameter +
    biradialTotalDensityQuadraticNormalForm a b row column *
      parameter ^ 2 +
    biradialTotalDensityCubicNormalForm a b row column *
      parameter ^ 3

theorem biradialTotalDensityPolynomial_coordinate_normalForm
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (row column : Fin 4) (parameter : ℝ) :
    biradialTotalDensityPolynomial a b
        (biradialCoframe a b +
          parameter • coframeCoordinateVariation row column) =
      biradialCoordinateDensityPolynomial
        a b row column parameter := by
  unfold biradialTotalDensityPolynomial
  rw [biradialCoframe_coordinate_det ha hb]
  fin_cases row <;> fin_cases column <;>
    simp [biradialGaugeBFPolynomial,
      biradialCoordinateDensityPolynomial,
      biradialTotalDensityConstant,
      biradialTotalDensityQuadraticNormalForm,
      biradialTotalDensityCubicNormalForm,
      biradialCoframeStressNormalForm,
      biradialCoframeDetCoordinateSlope,
      fixedCurvatureBiradialPointField,
      biradialP286AuxiliaryCoordinate_apply ha hb,
      referenceP286CurvatureCoordinate_apply,
      gravityBFPolynomial, gravityInternalDualEquiv,
      gravityInternalDualLinear, internalBivectorDual,
      StageNineGravityAuxiliaryVariation.gravityAuxiliaryHodgePairingPolynomial,
      p286GaugeAuxiliaryHodgePairingPolynomial,
      generatedGaugeTwoFormMetricPairing,
      physicalIIPlusBivector, coframeCoordinateVariation,
      biradialCoframe, coframeTwoFormLinear, coframeWedge,
      liftGaugeTwoFormOperator, gaugeOperatorCoefficient,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      minkowskiInternalSign, pairFirst, pairSecond,
      p286CoordinateLiePairing_smul_left,
      p286CoordinateLiePairing_smul_right,
      canonicalP286Generator_coordinatePairing_self,
      Matrix.diagonal_apply, Matrix.single,
      Fin.sum_univ_six] <;>
    field_simp [ha, hb] <;>
    ring

private theorem cubic_hasDerivAt_at_zero
    (constant linear quadratic cubic : ℝ) :
    HasDerivAt
      (fun parameter : ℝ =>
        constant + linear * parameter +
          quadratic * parameter ^ 2 +
          cubic * parameter ^ 3)
      linear 0 := by
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have polynomial :=
    (((hasDerivAt_const (x := (0 : ℝ)) constant).add
      (identityDerivative.const_mul linear)).add
      ((identityDerivative.pow 2).const_mul quadratic)).add
      ((identityDerivative.pow 3).const_mul cubic)
  convert! polynomial using 1
  all_goals simp only [id_eq]
  all_goals ring

theorem biradialCoordinateDensityPolynomial_hasDerivAt
    (a b : ℝ) (row column : Fin 4) :
    HasDerivAt
      (biradialCoordinateDensityPolynomial a b row column)
      (biradialCoframeStressNormalForm a b row column) 0 := by
  change HasDerivAt
    (fun parameter : ℝ =>
      biradialCoordinateDensityPolynomial
        a b row column parameter)
    (biradialCoframeStressNormalForm a b row column) 0
  simpa only [biradialCoordinateDensityPolynomial] using
    cubic_hasDerivAt_at_zero
      (biradialTotalDensityConstant a b)
      (biradialCoframeStressNormalForm a b row column)
      (biradialTotalDensityQuadraticNormalForm a b row column)
      (biradialTotalDensityCubicNormalForm a b row column)

private theorem biradialTotalDensityPolynomial_coordinate_hasDerivAt
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (row column : Fin 4) :
    HasDerivAt
      (fun parameter : ℝ =>
        biradialTotalDensityPolynomial a b
          (biradialCoframe a b +
            parameter • coframeCoordinateVariation row column))
      (biradialCoframeStressNormalForm a b row column) 0 := by
  have pathEquality :
      (fun parameter : ℝ =>
        biradialTotalDensityPolynomial a b
          (biradialCoframe a b +
            parameter • coframeCoordinateVariation row column)) =
        biradialCoordinateDensityPolynomial a b row column := by
    funext parameter
    exact
      biradialTotalDensityPolynomial_coordinate_normalForm
        ha hb row column parameter
  rw [pathEquality]
  exact
    biradialCoordinateDensityPolynomial_hasDerivAt
      a b row column

theorem fixedCurvatureBiradial_coframeStress_coordinate_normalForm
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (row column : Fin 4) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (fixedCurvatureBiradialPointField a b)
        (coframeCoordinateVariation row column) =
      biradialCoframeStressNormalForm a b row column := by
  have fieldNondegenerate :
      Matrix.det
        (fixedCurvatureBiradialPointField a b).coframe ≠ 0 := by
    change Matrix.det (biradialCoframe a b) ≠ 0
    rw [biradialCoframe_det]
    exact mul_ne_zero (pow_ne_zero 2 ha.ne') (pow_ne_zero 2 hb.ne')
  have outer :=
    coframeLocalDensity_hasFDerivAt
      positiveSmoothUnifiedSource 0
      (fixedCurvatureBiradialPointField a b)
      fieldNondegenerate
  have identityDerivative := hasDerivAt_id (x := (0 : ℝ))
  have coordinateDerivative :=
    identityDerivative.smul_const
      (coframeCoordinateVariation row column)
  have coordinateDerivativeValue :
      (1 : ℝ) • coframeCoordinateVariation row column =
        coframeCoordinateVariation row column := by
    simp
  have coordinateDerivativeAtZero :=
    coordinateDerivative.congr_deriv coordinateDerivativeValue
  have pathDerivative :=
    coordinateDerivativeAtZero.const_add (biradialCoframe a b)
  have pointEquality :
      (fixedCurvatureBiradialPointField a b).coframe =
        biradialCoframe a b +
          (0 : ℝ) • coframeCoordinateVariation row column := by
    simp [fixedCurvatureBiradialPointField]
  have composed :=
    outer.comp_hasDerivAt_of_eq
      (0 : ℝ) pathDerivative pointEquality
  have determinantContinuous :
      Continuous
        (fun parameter : ℝ =>
          Matrix.det
            (biradialCoframe a b +
              parameter • coframeCoordinateVariation row column)) :=
    StageNineCoframeVariation.coframe_det_contDiff.continuous.comp
      (by fun_prop)
  have determinantAtZero :
      0 <
        Matrix.det
          (biradialCoframe a b +
            (0 : ℝ) • coframeCoordinateVariation row column) := by
    simp only [zero_smul, add_zero]
    rw [biradialCoframe_det]
    positivity
  have eventuallyPositive :
      ∀ᶠ parameter in nhds (0 : ℝ),
        0 <
          Matrix.det
            (biradialCoframe a b +
              parameter • coframeCoordinateVariation row column) :=
    determinantContinuous.continuousAt.eventually
      (Ioi_mem_nhds determinantAtZero)
  have formulaEventually : Filter.EventuallyEq (nhds (0 : ℝ))
      (fun parameter : ℝ =>
        coframeLocalDensity positiveSmoothUnifiedSource 0
          (fixedCurvatureBiradialPointField a b)
          (biradialCoframe a b +
            parameter • coframeCoordinateVariation row column))
      (fun parameter : ℝ =>
        biradialTotalDensityPolynomial a b
          (biradialCoframe a b +
            parameter • coframeCoordinateVariation row column)) := by
    filter_upwards [eventuallyPositive] with parameter positive
    exact fixedCurvatureBiradial_localDensity_eq_polynomial
      _ positive
  have polynomialDerivative :=
    biradialTotalDensityPolynomial_coordinate_hasDerivAt
      ha.ne' hb.ne' row column
  have exactDerivative :=
    polynomialDerivative.congr_of_eventuallyEq formulaEventually
  exact composed.unique exactDerivative

theorem referenceOriginField_coframeStress_coordinate_biradialNormalForm
    (row column : Fin 4) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        referenceOriginField
        (coframeCoordinateVariation row column) =
      biradialCoframeStressNormalForm 1 1 row column := by
  rw [← fixedCurvatureBiradialPointField_one_one]
  exact fixedCurvatureBiradial_coframeStress_coordinate_normalForm
    (by norm_num) (by norm_num) row column

theorem fixedCurvatureBiradial_coframeStress_eq_half_reference_iff
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    coframeLocalStressCovector positiveSmoothUnifiedSource 0
        (fixedCurvatureBiradialPointField a b) =
      (1 / 2 : ℝ) •
        coframeLocalStressCovector positiveSmoothUnifiedSource 0
          referenceOriginField ↔
      BiradialBalance a b := by
  constructor
  · intro covectorEquality
    have coordinateEquality :=
      (coframeCovector_eq_iff_coordinateVariations _ _).1
        covectorEquality
    have timeCoordinate := coordinateEquality 0 0
    have spaceCoordinate := coordinateEquality 2 2
    rw [
      fixedCurvatureBiradial_coframeStress_coordinate_normalForm
        ha hb
    ] at timeCoordinate spaceCoordinate
    simp only [smul_apply, smul_eq_mul] at timeCoordinate spaceCoordinate
    rw [
      referenceOriginField_coframeStress_coordinate_biradialNormalForm
    ] at timeCoordinate spaceCoordinate
    simp [biradialCoframeStressNormalForm] at timeCoordinate spaceCoordinate
    apply (biradialBalance_iff_expanded a b).2
    constructor <;> nlinarith
  · intro balance
    apply (coframeCovector_eq_iff_coordinateVariations _ _).2
    intro row column
    rw [
      fixedCurvatureBiradial_coframeStress_coordinate_normalForm
        ha hb
    ]
    simp only [smul_apply, smul_eq_mul]
    rw [
      referenceOriginField_coframeStress_coordinate_biradialNormalForm
    ]
    have expanded := (biradialBalance_iff_expanded a b).1 balance
    fin_cases row <;> fin_cases column <;>
      simp [biradialCoframeStressNormalForm] <;>
      nlinarith [expanded.1, expanded.2]

theorem existsUnique_positive_biradialCoframe_half_referenceStress :
    ∃! p : ℝ × ℝ,
      0 < p.1 ∧
        0 < p.2 ∧
          coframeLocalStressCovector positiveSmoothUnifiedSource 0
              (fixedCurvatureBiradialPointField p.1 p.2) =
            (1 / 2 : ℝ) •
              coframeLocalStressCovector positiveSmoothUnifiedSource 0
                referenceOriginField := by
  rcases existsUnique_positive_biradialBalance with
    ⟨parameters, positiveBalance, unique⟩
  refine ⟨parameters, ?_, ?_⟩
  · exact ⟨positiveBalance.1, positiveBalance.2.1,
      (fixedCurvatureBiradial_coframeStress_eq_half_reference_iff
        positiveBalance.1 positiveBalance.2.1).2 positiveBalance.2.2⟩
  · intro candidate candidateProperty
    apply unique candidate
    exact ⟨candidateProperty.1, candidateProperty.2.1,
      (fixedCurvatureBiradial_coframeStress_eq_half_reference_iff
        candidateProperty.1 candidateProperty.2.1).1
          candidateProperty.2.2⟩

end

end SaturationMonoid.PhysicsCore.StageNineBiradialCoframeResponse
