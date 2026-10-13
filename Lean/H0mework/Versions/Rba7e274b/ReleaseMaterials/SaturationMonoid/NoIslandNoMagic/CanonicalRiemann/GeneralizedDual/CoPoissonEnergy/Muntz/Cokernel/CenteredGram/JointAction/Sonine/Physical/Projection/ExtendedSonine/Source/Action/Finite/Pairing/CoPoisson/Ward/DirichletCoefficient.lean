import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DirichletCoefficient

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology
noncomputable section

private def floorDefect (x : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator (fun x => ((Int.fract x : ℝ) : ℂ)) x

private def errorIntegrand (s : ℂ) (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

private theorem defect_measurable : Measurable floorDefect := by
  unfold floorDefect
  apply Measurable.indicator _ measurableSet_Ioi
  unfold Int.fract
  fun_prop

private theorem defect_bound (x : ℝ) : ‖floorDefect x‖ ≤ 1 := by
  unfold floorDefect
  by_cases inside : x ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem inside, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  · rw [indicator_of_notMem inside, norm_zero]
    norm_num

private theorem defect_locallyIntegrable : LocallyIntegrableOn floorDefect (Ioi 0) :=
  (locallyIntegrableOn_const (1 : ℂ)).mono defect_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa using defect_bound x))

private theorem defect_top : floorDefect =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards with x
  simpa using defect_bound x

private theorem defect_zero (exponent : ℝ) :
    floorDefect =O[𝓝[>] 0] (fun x : ℝ => x ^ (-exponent)) := by
  apply (isBigO_zero (fun x : ℝ => x ^ (-exponent)) (𝓝[>] 0)).congr' _ Filter.EventuallyEq.rfl
  have small : Iio (1 : ℝ) ∈ (𝓝[>] (0 : ℝ)) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [small] with x inside
  have outside : x ∉ Ioi (1 : ℝ) := by
    change ¬ 1 < x
    exact not_lt.mpr (show x < 1 from inside).le
  simp only [floorDefect, indicator_of_notMem outside]

private theorem defect_mellinConvergent (s : ℂ) (positive : 0 < s.re) :
    MellinConvergent floorDefect (-s) :=
  mellinConvergent_of_isBigO_rpow defect_locallyIntegrable defect_top
    (by simpa using neg_neg_of_pos positive) (defect_zero (-s.re - 1)) (by simp)

private theorem defect_mellin_eq (s : ℂ) :
    mellin floorDefect (-s) = ∫ x : ℝ in Ioi 1, errorIntegrand s x := by
  have integrand : (fun x : ℝ => (x : ℂ) ^ (-s - 1) • floorDefect x) =
      (Ioi (1 : ℝ)).indicator (errorIntegrand s) := by
    ext x
    by_cases inside : x ∈ Ioi (1 : ℝ)
    · simp [floorDefect, indicator_of_mem inside, errorIntegrand, smul_eq_mul, mul_comm]
    · simp [floorDefect, indicator_of_notMem inside]
  unfold mellin
  rw [integrand, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]

private theorem error_integrable (s : ℂ) (positive : 0 < s.re) :
    IntegrableOn (errorIntegrand s) (Ioi 1) := by
  have native := (defect_mellinConvergent s positive).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  apply native.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
  simp [floorDefect, indicator_of_mem inside, errorIntegrand, smul_eq_mul, mul_comm]

private theorem defect_mellin_differentiable (s : ℂ) (positive : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin floorDefect (-z)) s := by
  exact (mellin_differentiableAt_of_isBigO_rpow defect_locallyIntegrable defect_top
    (show (-s).re < 0 by simpa using neg_neg_of_pos positive)
    (defect_zero (-s.re - 1)) (by simp)).comp s (differentiableAt_id.neg)

private theorem power_zero (s : ℂ) (positive : 0 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have bound := (tendsto_rpow_neg_atTop positive).comp tendsto_natCast_atTop_atTop
  apply bound.congr'
  filter_upwards [eventually_ge_atTop 1] with N after
  rw [Complex.norm_natCast_cpow_of_pos (Nat.lt_of_lt_of_le (by decide : 0 < 1) after), neg_re]
  rfl

private def unitCoefficient (n : ℕ) : ℂ := if n = 0 then 0 else 1

private theorem unitCoefficient_sum (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, unitCoefficient n) = (N : ℂ) := by
  induction N with
  | zero => simp [unitCoefficient]
  | succ N previous =>
    rw [Finset.sum_Icc_succ_top (by omega), previous]
    simp [unitCoefficient]

private theorem unitCoefficient_weighted (s : ℂ) (N : ℕ) (positive : 0 < N) :
    (∑ n ∈ Finset.Icc 0 N, (n : ℂ) ^ (-s) * unitCoefficient n) =
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (-s) := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
  simp only [unitCoefficient, ite_true, mul_zero, zero_add]
  rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add,
    ← Finset.sum_Ico_add_eq_sum_Icc (Nat.one_le_iff_ne_zero.mpr positive.ne')]
  congr 1
  · apply Finset.sum_congr rfl
    intro n inside
    rw [if_neg (by have := (Finset.mem_Ico.mp inside).1; omega : n ≠ 0), mul_one]
  · rw [if_neg positive.ne', mul_one]

private theorem coefficient_euler (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1)
    (N : ℕ) (indexPositive : 0 < N) :
    FiniteForcing.coefficient s N = s / (s - 1) - (N : ℂ) ^ (-s) -
      s * ∫ x : ℝ in Ioc 1 (N : ℝ), errorIntegrand s x := by
  have sNonzero : s ≠ 0 := by intro h; simp [h] at positive
  have upper : (1 : ℝ) ≤ N := by exact_mod_cast indexPositive
  have intervalNonzero : (0 : ℝ) ∉ uIcc 1 (N : ℝ) := by
    rw [uIcc_of_le upper]
    simp
  have powerIntegral : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr intervalNonzero)
  have derivativeIntegral : IntervalIntegrable (fun x : ℝ => -s * (x : ℂ) ^ (-s - 1)) volume 1 N :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr intervalNonzero)).const_mul (-s)
  have derivative (x : ℝ) (inside : x ∈ Icc 1 (N : ℝ)) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const (by linarith [inside.1]) (neg_ne_zero.mpr sNonzero)
  have actualDerivativeIntegral : IntegrableOn (deriv (fun x : ℝ => (x : ℂ) ^ (-s))) (Icc 1 (N : ℝ)) := by
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le upper).mp derivativeIntegral).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x inside
    exact (derivative x inside).deriv.symm
  have abel := sum_mul_eq_sub_integral_mul₀' unitCoefficient (by simp [unitCoefficient]) N
    (fun x inside => (derivative x inside).differentiableAt) actualDerivativeIntegral
  simp only [Complex.ofReal_natCast] at abel
  rw [unitCoefficient_weighted s N indexPositive, unitCoefficient_sum] at abel
  simp only [unitCoefficient_sum] at abel
  have transformed : (∫ x : ℝ in Ioc 1 (N : ℝ),
      deriv (fun y : ℝ => (y : ℂ) ^ (-s)) x * (⌊x⌋₊ : ℂ)) =
        -s * ((∫ x : ℝ in Ioc 1 (N : ℝ), (x : ℂ) ^ (-s)) -
          ∫ x : ℝ in Ioc 1 (N : ℝ), errorIntegrand s x) := by
    have integrand : ∀ x ∈ Ioc 1 (N : ℝ),
        deriv (fun y : ℝ => (y : ℂ) ^ (-s)) x * (⌊x⌋₊ : ℂ) =
          -s * ((x : ℂ) ^ (-s) - errorIntegrand s x) := by
      intro x inside
      have xPositive : 0 < x := zero_lt_one.trans inside.1
      have floorRead : (⌊x⌋₊ : ℂ) = (x : ℂ) - ((Int.fract x : ℝ) : ℂ) := by
        have source : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
          rw [natCast_floor_eq_intCast_floor xPositive.le]
          simp only [Int.fract, sub_sub_cancel]
        exact_mod_cast source
      have powerRead : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * (x : ℂ) := by
        simpa only [sub_add_cancel, cpow_one] using
          (Complex.cpow_add (-s - 1) 1 (Complex.ofReal_ne_zero.mpr xPositive.ne'))
      rw [(derivative x ⟨inside.1.le, inside.2⟩).deriv, floorRead, powerRead, errorIntegrand]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc integrand, integral_const_mul,
      integral_sub powerIntegral.1
        ((error_integrable s positive).mono_set (fun _ inside => inside.1))]
  rw [transformed] at abel
  have powerRead : (∫ x : ℝ in Ioc 1 (N : ℝ), (x : ℂ) ^ (-s)) =
      ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    rw [← intervalIntegral.integral_of_le upper,
      integral_cpow (Or.inr ⟨by simpa using notOne, intervalNonzero⟩),
      show -s + 1 = 1 - s by ring, Complex.ofReal_one, one_cpow, Complex.ofReal_natCast]
  rw [powerRead] at abel
  have head : (N : ℂ) ^ (1 - s) = (N : ℂ) ^ (-s) * (N : ℂ) := by
    rw [show 1 - s = -s + 1 by ring,
      Complex.cpow_add _ _ (by exact_mod_cast indexPositive.ne'), cpow_one]
  unfold FiniteForcing.coefficient
  rw [head] at abel ⊢
  have denominator : 1 - s ≠ 0 := sub_ne_zero.mpr notOne.symm
  have denominator' : s - 1 ≠ 0 := sub_ne_zero.mpr notOne
  field_simp [denominator, denominator'] at abel ⊢
  linear_combination (s - 1) * abel

private theorem coefficient_tendsto_integral (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1) :
    Tendsto (FiniteForcing.coefficient s) atTop
      (𝓝 (s / (s - 1) - s * mellin floorDefect (-s))) := by
  have integralLimit := intervalIntegral_tendsto_integral_Ioi 1 (error_integrable s positive)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have result := ((tendsto_const_nhds (x := s / (s - 1))).sub
    (power_zero s positive)).sub (integralLimit.const_mul s)
  rw [defect_mellin_eq]
  simpa only [sub_zero] using! result.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N after
    rw [intervalIntegral.integral_of_le (by exact_mod_cast after)]
    exact (coefficient_euler s positive notOne N
      (Nat.lt_of_lt_of_le (by decide : 0 < 1) after)).symm)

private theorem coefficient_tendsto_dirichlet (s : ℂ) (convergent : 1 < s.re) :
    Tendsto (FiniteForcing.coefficient s) atTop (𝓝 (riemannZeta s)) := by
  have sNonzero : s ≠ 0 := by intro h; norm_num [h] at convergent
  have summable : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    simpa only [Complex.cpow_neg, one_div] using (Complex.summable_one_div_nat_cpow.mpr convergent)
  have value : (∑' n : ℕ, (n : ℂ) ^ (-s)) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_cpow convergent]
    simp only [Complex.cpow_neg, one_div]
  have discrete : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    have actual := summable.hasSum.tendsto_sum_nat
    rw [value] at actual
    apply actual.congr'
    filter_upwards [eventually_ge_atTop 1] with N after
    rw [Finset.sum_Ico_eq_sub _ after]
    simp only [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr sNonzero), sub_zero]
  have tail := (power_zero (s - 1) (by simp only [sub_re, one_re]; linarith)).div_const (1 - s)
  have result := discrete.sub tail
  simpa only [neg_sub, zero_div, sub_zero, FiniteForcing.coefficient] using! result

private theorem source_mellin_eq_zeta (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1) :
    s / (s - 1) - s * mellin floorDefect (-s) = riemannZeta s := by
  let domain := {z : ℂ | 0 < z.re}
  let formula := fun z : ℂ => z - z * (z - 1) * mellin floorDefect (-z)
  have openDomain : IsOpen domain := isOpen_lt continuous_const Complex.continuous_re
  have analyticOwner : AnalyticOnNhd ℂ riemannZeta₁ domain :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd openDomain
  have analyticSource : AnalyticOnNhd ℂ formula domain := by
    apply DifferentiableOn.analyticOnNhd _ openDomain
    intro z inside
    have actual := defect_mellin_differentiable z inside
    exact ((differentiableAt_id).sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul actual)).differentiableWithinAt
  have owner (z : ℂ) (notPole : z ≠ 1) : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul notPole, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr notPole), one_mul]
  have agreement (z : ℂ) (convergent : 1 < z.re) : riemannZeta₁ z = formula z := by
    have notPole : z ≠ 1 := by intro h; simp [h] at convergent
    have same := tendsto_nhds_unique (coefficient_tendsto_dirichlet z convergent)
      (coefficient_tendsto_integral z (zero_lt_one.trans convergent) notPole)
    rw [owner z notPole, same]
    unfold formula
    field_simp
  have same := analyticOwner.eqOn_of_preconnected_of_eventuallyEq analyticSource
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
    (show (2 : ℂ) ∈ domain by norm_num [domain])
    (eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)) agreement)
  have atSource := same positive
  rw [owner s notOne] at atSource
  dsimp only [formula] at atSource
  have denominator := sub_ne_zero.mpr notOne
  field_simp [denominator]
  linear_combination -atSource

/-- The actual integer-minus-continuous coefficient converges to the original
theta-defined zeta throughout Re s > 0, away from its pole. -/
theorem coefficient_tendsto_riemannZeta (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1) :
    Tendsto (FiniteForcing.coefficient s) atTop (𝓝 (riemannZeta s)) := by
  rw [← source_mellin_eq_zeta s positive notOne]
  exact coefficient_tendsto_integral s positive notOne

/-- Both same-zero arithmetic coefficients are paid by the original zeta
occurrence and its existing functional equation. -/
theorem original_coefficient_limits (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (FiniteForcing.coefficient (star coordinate.value)) atTop (𝓝 0) ∧
      Tendsto (FiniteForcing.coefficient (1 - star coordinate.value)) atTop (𝓝 0) := by
  have positive : 0 < (star coordinate.value).re := by
    simp only [star_def, conj_re]
    linarith [coordinate.rightHalf]
  have below : (star coordinate.value).re < 1 := by
    simpa only [star_def, conj_re] using coordinate.belowOne
  have notOne : star coordinate.value ≠ 1 := by intro h; simp [h] at below
  have selected : riemannZeta (star coordinate.value) = 0 := by
    simpa only [star_def, zero, map_zero] using riemannZeta_conj coordinate.value
  have reversed : riemannZeta (1 - star coordinate.value) = 0 := by
    rw [riemannZeta_one_sub ?_ notOne, selected, mul_zero]
    intro n equality
    have actual := congrArg Complex.re equality
    simp only [neg_re, natCast_re] at actual
    have nonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  constructor
  · simpa only [selected] using coefficient_tendsto_riemannZeta (star coordinate.value) positive notOne
  · have positive' : 0 < (1 - star coordinate.value).re := by simp only [sub_re, one_re]; linarith
    have notOne' : 1 - star coordinate.value ≠ 1 := by
      intro h
      have actual := congrArg Complex.re h
      simp only [sub_re, one_re] at actual
      linarith
    simpa only [reversed] using coefficient_tendsto_riemannZeta (1 - star coordinate.value) positive' notOne'

/-- The source-generated arithmetic limits remove both coefficient terms
from the original signed read, retaining the complete paired forcing. -/
theorem original_forcing_balance_tendsto_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    Tendsto (fun N : ℕ =>
      inner ℂ (positionSeed coordinate shift) (FiniteForcing.positionForcing coordinate N) -
        inner ℂ (fourierSeed coordinate shift) (FiniteForcing.fourierForcing coordinate N)) atTop (𝓝 0) := by
  have coefficients := original_coefficient_limits coordinate zero
  have arithmetic :=
    (coefficients.1.mul_const
      (inner ℂ (positionSeed coordinate shift) (burnolCompletedMellinRieszVector coordinate : BurnolL2))).sub
    (coefficients.2.mul_const
      (inner ℂ (fourierSeed coordinate shift)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))))
  have original := FiniteForcing.signed_source_tendsto_zero coordinate zero shift nonnegative bounded
  have cancelled := original.sub arithmetic
  convert cancelled using 1
  · funext N
    ring
  · simp

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DirichletCoefficient
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
