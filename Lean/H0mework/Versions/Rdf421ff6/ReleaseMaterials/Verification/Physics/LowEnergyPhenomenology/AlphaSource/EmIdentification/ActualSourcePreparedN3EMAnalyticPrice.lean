import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMChargeRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3EMAnalyticPrice
open Polynomial CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualCompositeFieldCurrent
open PhysicalN3SourceEnergy ActualSourcePreparedN3EMChargeRead
open ActualSourcePreparedN3EMIRSplit ActualSourcePreparedEMEnclosure
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open ActualDressedZeroDamping ActualDressedNoetherCoulombUnit
open ActualDressedEMTensorClock
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators

/-- The constant term is excluded; every other source coefficient is retained. -/
def polynomialTailPrice (P : ℂ[X]) : ℝ :=
  ∑ k ∈ (P.erase 0).support, ‖(P.erase 0).coeff k‖

private theorem polynomial_tail_price_nonnegative (P : ℂ[X]) : 0 ≤ polynomialTailPrice P :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem polynomial_tail_price (P : ℂ[X]) (z : ℂ) (small : ‖z‖ ≤ 1) :
    ‖P.eval z-P.coeff 0‖ ≤ polynomialTailPrice P * ‖z‖ := by
  have split := congrArg (fun Q : ℂ[X] => Q.eval z) (monomial_add_erase P 0)
  simp only [eval_add, eval_monomial, pow_zero, mul_one] at split
  have difference : P.eval z-P.coeff 0 = (P.erase 0).eval z := by
    linear_combination -split
  rw [difference, eval_eq_sum]
  unfold Polynomial.sum
  apply (norm_sum_le _ _).trans
  unfold polynomialTailPrice
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k inside
  have nonzero : k ≠ 0 := by
    rw [support_erase] at inside
    exact (Finset.mem_erase.mp inside).1
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one (norm_nonneg z) small nonzero) (norm_nonneg _)

def polynomialReadRadius (B : ℂ[X]) : ℝ :=
  min 1 (‖B.coeff 0‖/(2*(1+polynomialTailPrice B)))

theorem polynomial_read_radius_positive (B : ℂ[X]) (nonzero : B.coeff 0 ≠ 0) :
    0 < polynomialReadRadius B := by
  have budget := polynomial_tail_price_nonnegative B
  unfold polynomialReadRadius
  exact lt_min (by norm_num) (div_pos (norm_pos_iff.mpr nonzero) (by positivity))

theorem polynomial_read_margin (B : ℂ[X]) (nonzero : B.coeff 0 ≠ 0)
    (z : ℂ) (small : ‖z‖ ≤ polynomialReadRadius B) :
    ‖B.coeff 0‖/2 ≤ ‖B.eval z‖ := by
  have budget := polynomial_tail_price_nonnegative B
  have radius := (polynomial_read_radius_positive B nonzero).le
  have unit : ‖z‖ ≤ 1 := small.trans (min_le_left _ _)
  have denominator : 0 < 2*(1+polynomialTailPrice B) := by positivity
  have cap : 2*(1+polynomialTailPrice B)*polynomialReadRadius B ≤ ‖B.coeff 0‖ := by
    have bound : polynomialReadRadius B ≤ ‖B.coeff 0‖/(2*(1+polynomialTailPrice B)) := min_le_right _ _
    have multiplied := (le_div_iff₀ denominator).mp bound
    nlinarith
  have displacement := (polynomial_tail_price B z unit).trans
    (mul_le_mul_of_nonneg_left small budget)
  have reverse := norm_sub_norm_le (B.coeff 0) (B.eval z)
  rw [norm_sub_rev] at reverse
  nlinarith

def polynomialRatioSlope (A B : ℂ[X]) : ℝ :=
  2*(‖B.coeff 0‖*polynomialTailPrice A+‖A.coeff 0‖*polynomialTailPrice B)/‖B.coeff 0‖^2

theorem polynomial_ratio_price (A B : ℂ[X]) (nonzero : B.coeff 0 ≠ 0)
    (z : ℂ) (small : ‖z‖ ≤ polynomialReadRadius B) :
    ‖A.eval z/B.eval z-A.coeff 0/B.coeff 0‖ ≤ polynomialRatioSlope A B * ‖z‖ := by
  have center := norm_pos_iff.mpr nonzero
  have margin := polynomial_read_margin B nonzero z small
  have value : B.eval z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (half_pos center) margin)
  have unit : ‖z‖ ≤ 1 := small.trans (min_le_left _ _)
  have aError := polynomial_tail_price A z unit
  have bError := polynomial_tail_price B z unit
  have split : A.eval z/B.eval z-A.coeff 0/B.coeff 0 =
      ((A.eval z-A.coeff 0)*B.coeff 0+A.coeff 0*(B.coeff 0-B.eval z))/(B.eval z*B.coeff 0) := by
    field_simp [nonzero, value]
    ring
  have numerator : ‖(A.eval z-A.coeff 0)*B.coeff 0+A.coeff 0*(B.coeff 0-B.eval z)‖ ≤
      (‖B.coeff 0‖*polynomialTailPrice A+‖A.coeff 0‖*polynomialTailPrice B)*‖z‖ := by
    have aPaid := mul_le_mul_of_nonneg_right aError (norm_nonneg (B.coeff 0))
    have bPaid := mul_le_mul_of_nonneg_left bError (norm_nonneg (A.coeff 0))
    calc
      _ ≤ ‖(A.eval z-A.coeff 0)*B.coeff 0‖ +
          ‖A.coeff 0*(B.coeff 0-B.eval z)‖ := norm_add_le _ _
      _ = ‖A.eval z-A.coeff 0‖*‖B.coeff 0‖ +
          ‖A.coeff 0‖*‖B.eval z-B.coeff 0‖ := by
        rw [norm_mul, norm_mul, norm_sub_rev (B.coeff 0) (B.eval z)]
      _ ≤ polynomialTailPrice A * ‖z‖ * ‖B.coeff 0‖ +
          ‖A.coeff 0‖ * (polynomialTailPrice B * ‖z‖) := add_le_add aPaid bPaid
      _ = (‖B.coeff 0‖*polynomialTailPrice A+‖A.coeff 0‖*polynomialTailPrice B)*‖z‖ := by ring
  have denominator : ‖B.coeff 0‖^2/2 ≤ ‖B.eval z‖*‖B.coeff 0‖ := by
    have paid := mul_le_mul_of_nonneg_right margin (norm_nonneg (B.coeff 0))
    nlinarith
  have lower : 0 < ‖B.coeff 0‖^2/2 := by positivity
  have bound_nonnegative : 0 ≤
      (‖B.coeff 0‖*polynomialTailPrice A+‖A.coeff 0‖*polynomialTailPrice B)*‖z‖ := by
    have aBudget := polynomial_tail_price_nonnegative A
    have bBudget := polynomial_tail_price_nonnegative B
    positivity
  rw [split, norm_div, norm_mul]
  calc
    _ ≤ ((‖B.coeff 0‖*polynomialTailPrice A+‖A.coeff 0‖*polynomialTailPrice B)*‖z‖)/
        (‖B.eval z‖*‖B.coeff 0‖) := div_le_div_of_nonneg_right numerator (by positivity)
    _ ≤ ((‖B.coeff 0‖*polynomialTailPrice A+‖A.coeff 0‖*polynomialTailPrice B)*‖z‖)/
        (‖B.coeff 0‖^2/2) := div_le_div_of_nonneg_left bound_nonnegative lower denominator
    _ = _ := by unfold polynomialRatioSlope; field_simp

def sourceEMAnalyticRadius (R : RatFunc ℂ) : ℝ := polynomialReadRadius (rootRemainder R 0)

def sourceEMAnalyticCenter (R : RatFunc ℂ) : ℂ :=
  (analyticNumerator R 0).coeff 0/(rootRemainder R 0).coeff 0

def sourceEMAnalyticSlope (R : RatFunc ℂ) : ℝ :=
  polynomialRatioSlope (analyticNumerator R 0) (rootRemainder R 0)

theorem source_em_analytic_price (R : RatFunc ℂ) (z : ℂ) (small : ‖z‖ ≤ sourceEMAnalyticRadius R) :
    0 < sourceEMAnalyticRadius R ∧
    ‖(analyticNumerator R 0).eval z/(rootRemainder R 0).eval z-sourceEMAnalyticCenter R‖ ≤
      sourceEMAnalyticSlope R * ‖z‖ := by
  have nonzero : (rootRemainder R 0).coeff 0 ≠ 0 := by
    simpa only [← coeff_zero_eq_eval_zero] using root_remainder_nonzero R 0
  exact ⟨polynomial_read_radius_positive _ nonzero,
    polynomial_ratio_price _ _ nonzero z small⟩

/-- The complete clock principal is retained before pricing the analytic
remainder of the actual pure EM Noether read. No zero pole order is assumed. -/
theorem source_n3_em_principal_analytic_price (fieldEvent detector source : DressedEvent)
    (epsilon sigma : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (positive : 0 < sigma)
    (chart : (dampingDeterminant fieldEvent epsilon n).eval (sigma : ℂ) ≠ 0)
    (small : ‖(sigma : ℂ)‖ ≤ sourceEMAnalyticRadius
      (sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true true)) :
    let R := sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true true
    0 < sourceEMAnalyticRadius R ∧
    ‖dotProduct (physicalN3PoleNoetherCurrent detector dLeg dPoles)
        ((noetherPairScale^2 • sourcePreparedEMTensorRead fieldEvent epsilon sigma n) *ᵥ
          physicalN3PoleNoetherCurrent source sLeg sPoles) -
      (principalNumerator R 0).eval (sigma : ℂ)/(sigma : ℂ)^poleOrder R 0 -
        sourceEMAnalyticCenter R‖ ≤ sourceEMAnalyticSlope R * ‖(sigma : ℂ)‖ := by
  let R := sourceN3ArmDampingFraction fieldEvent detector source epsilon n dLeg sLeg dPoles sPoles true true
  have price := source_em_analytic_price R (sigma : ℂ) small
  have center : (rootRemainder R 0).coeff 0 ≠ 0 := by
    simpa only [← coeff_zero_eq_eval_zero] using root_remainder_nonzero R 0
  have margin := polynomial_read_margin (rootRemainder R 0) center (sigma : ℂ) small
  have remainder : (rootRemainder R 0).eval (sigma : ℂ) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (half_pos (norm_pos_iff.mpr center)) margin)
  have away : (sigma : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt positive)
  have principal := complete_principal_part R 0 (sigma : ℂ) away remainder
  simp only [sub_zero] at principal
  have commonRegular : MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant fieldEvent n) ≠ 0 := by
    rw [← damping_slice_eval]
    exact chart
  have regular := actual_common_chart_original fieldEvent epsilon sigma 0 n positive commonRegular
  have read := source_n3_arm_damping_read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles true true positive chart
  rw [source_n3_em_arm_noether_read fieldEvent detector source epsilon sigma n dLeg sLeg dPoles sPoles positive regular] at read
  refine ⟨price.1, ?_⟩
  rw [read, principal]
  simpa only [R, add_sub_cancel_left] using price.2

end LowEnergy.GaussComposite.ActualSourcePreparedN3EMAnalyticPrice
