import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.DirichletRate

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section

private def errorIntegrand (s : ℂ) (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

private theorem error_bound (s : ℂ) (x : ℝ) (positive : 0 < x) :
    ‖errorIntegrand s x‖ ≤ x ^ (-s.re - 1) := by
  rw [errorIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg x), Complex.norm_cpow_eq_rpow_re_of_pos positive]
  simp only [sub_re, neg_re, one_re]
  exact (mul_le_mul_of_nonneg_right (Int.fract_lt_one x).le (Real.rpow_nonneg positive.le _)).trans_eq (one_mul _)

private theorem error_measurable (s : ℂ) : Measurable (errorIntegrand s) := by
  have power : Measurable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const x (-s - 1)
      (Or.inr (by simpa only [mem_compl_iff, mem_singleton_iff] using outside))).continuousWithinAt
  unfold errorIntegrand Int.fract
  fun_prop

private theorem error_integrable (s : ℂ) (positive : 0 < s.re) :
    IntegrableOn (errorIntegrand s) (Ioi 1) := by
  have bound : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
  apply bound.mono' (error_measurable s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
  exact error_bound s x (zero_lt_one.trans inside)

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

private theorem power_zero (s : ℂ) (positive : 0 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (-s)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have actual := (tendsto_rpow_neg_atTop positive).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply actual.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N after
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < N), neg_re]
  rfl

private theorem zeta_euler (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * ∫ x : ℝ in Ioi 1, errorIntegrand s x := by
  have integrals := intervalIntegral_tendsto_integral_Ioi 1 (error_integrable s positive)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have actual := ((tendsto_const_nhds (x := s / (s - 1))).sub (power_zero s positive)).sub
    (integrals.const_mul s)
  simp only [sub_zero] at actual
  have finite := actual.congr' (show _ =ᶠ[atTop] FiniteForcing.coefficient s from by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N after
    rw [intervalIntegral.integral_of_le (by exact_mod_cast after)]
    exact (coefficient_euler s positive notOne N (by omega)).symm)
  exact tendsto_nhds_unique (DirichletCoefficient.coefficient_tendsto_riemannZeta s positive notOne) finite

private theorem coefficient_error (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1)
    (N : ℕ) (indexPositive : 0 < N) :
    FiniteForcing.coefficient s N - riemannZeta s =
      -(N : ℂ) ^ (-s) + s * ∫ x : ℝ in Ioi (N : ℝ), errorIntegrand s x := by
  have upper : (1 : ℝ) ≤ N := by exact_mod_cast indexPositive
  have split := intervalIntegral.integral_Ioi_sub_Ioi (error_integrable s positive) upper
  rw [intervalIntegral.integral_of_le upper] at split
  rw [coefficient_euler s positive notOne N indexPositive, zeta_euler s positive notOne, ← split]
  ring

private theorem error_tail_bound (s : ℂ) (positive : 0 < s.re) (N : ℕ) (indexPositive : 0 < N) :
    ‖∫ x : ℝ in Ioi (N : ℝ), errorIntegrand s x‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have basePositive : (0 : ℝ) < N := by exact_mod_cast indexPositive
  have power : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_iff basePositive).mpr (by linarith)
  have actual := norm_integral_le_of_norm_le power (show ∀ᵐ x ∂volume.restrict (Ioi (N : ℝ)),
      ‖errorIntegrand s x‖ ≤ x ^ (-s.re - 1) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x inside
    exact error_bound s x (basePositive.trans inside))
  rw [integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) basePositive,
    show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq] at actual
  exact actual

/-- The constant is computed from the actual coordinate and its positive real part. -/
def constant (s : ℂ) : ℝ := 1 + ‖s‖ / s.re

/-- The original same-N Dirichlet coefficient has the quantitative tail supplied by its Abel source. -/
theorem coefficient_error_bound (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1)
    (N : ℕ) (indexPositive : 0 < N) :
    ‖FiniteForcing.coefficient s N - riemannZeta s‖ ≤ constant s * (N : ℝ) ^ (-s.re) := by
  rw [coefficient_error s positive notOne N indexPositive]
  calc
    _ ≤ ‖-(N : ℂ) ^ (-s)‖ + ‖s * ∫ x : ℝ in Ioi (N : ℝ), errorIntegrand s x‖ := norm_add_le _ _
    _ = (N : ℝ) ^ (-s.re) + ‖s‖ * ‖∫ x : ℝ in Ioi (N : ℝ), errorIntegrand s x‖ := by
      rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos indexPositive, neg_re]
    _ ≤ (N : ℝ) ^ (-s.re) + ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (error_tail_bound s positive N indexPositive) (norm_nonneg s))
    _ = _ := by unfold constant; ring

/-- The strip mouth derives pole exclusion from the source coordinate itself. -/
theorem coefficient_rate (s : ℂ) (positive : 0 < s.re) (below : s.re < 1)
    (N : ℕ) (indexPositive : 0 < N) :
    ‖FiniteForcing.coefficient s N - riemannZeta s‖ ≤ constant s * (N : ℝ) ^ (-s.re) := by
  have notOne : s ≠ 1 := by intro equality; simp [equality] at below
  exact coefficient_error_bound s positive notOne N indexPositive

/-- The original reversal-zero occurrence supplies the same rate at 1 - star c, with the same cutoff N. -/
theorem original_reverse_rate (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (N : ℕ) (indexPositive : 0 < N) :
    ‖FiniteForcing.coefficient (1 - star coordinate.value) N‖ ≤
      constant (1 - star coordinate.value) * (N : ℝ) ^ (coordinate.value.re - 1) := by
  have positive : 0 < (1 - star coordinate.value).re := by
    simp only [sub_re, one_re, star_def, conj_re]
    linarith [coordinate.belowOne]
  have below : (1 - star coordinate.value).re < 1 := by
    simp only [sub_re, one_re, star_def, conj_re]
    linarith [coordinate.rightHalf]
  have notOne : 1 - star coordinate.value ≠ 1 := by
    intro equality
    have realPart := congrArg Complex.re equality
    simp only [sub_re, one_re, star_def, conj_re] at realPart
    linarith [coordinate.rightHalf]
  have selected : riemannZeta (1 - star coordinate.value) = 0 := tendsto_nhds_unique
    (DirichletCoefficient.coefficient_tendsto_riemannZeta (1 - star coordinate.value) positive notOne)
    (DirichletCoefficient.original_coefficient_limits coordinate zero).2
  have actual := coefficient_rate (1 - star coordinate.value) positive below N indexPositive
  rw [selected, sub_zero] at actual
  simpa only [sub_re, one_re, star_def, conj_re, neg_sub] using actual

end
end OriginalRieszFinitePairing.CoPoisson.Ward.DirichletRate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
