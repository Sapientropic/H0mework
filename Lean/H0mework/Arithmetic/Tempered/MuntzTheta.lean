import Mathlib.NumberTheory.LSeries.RiemannZeta
import H0mework.Arithmetic.CoPoisson.MellinConvergence

/-!
# Arbitrary-Schwartz theta kernel for the co-Poisson--Müntz bridge

This file builds the actual nonzero theta sum and scale remainder, proves
Poisson reciprocity, and establishes rapid positive-scale decay from
Schwartz seminorms.  It assumes no zero or critical-line statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex FourierTransform MeasureTheory Set Filter Asymptotics
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace Topology

noncomputable section

def coPoissonMuntzThetaNonzero
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) : ℂ :=
  ∑' n : {n : ℤ // n ≠ 0}, test (scale * (n.1 : ℝ))

/-- The full theta kernel, stored using its nonzero sum and its literal zero mode. -/
def coPoissonMuntzTheta
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) : ℂ :=
  coPoissonMuntzThetaNonzero test scale + test 0

/-- The scale remainder, extended by zero away from positive scales. -/
def coPoissonMuntzScaleRemainder
    (test : SchwartzMap ℝ ℂ) (scale : ℝ) : ℂ :=
  if positive : 0 < scale then
    clozelTemperedRemainder
      (scaledSchwartzTest scale positive.ne' test)
  else 0

theorem coPoissonMuntzThetaNonzero_summable
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (scale_ne : scale ≠ 0) :
    Summable (fun n : {n : ℤ // n ≠ 0} =>
      test (scale * (n.1 : ℝ))) := by
  have source := summable_integer_evaluation
    (scaledSchwartzTest scale scale_ne test)
  exact (source.subtype (fun n : ℤ => n ≠ 0)).congr fun n => by
    simp only [Function.comp_apply, scaledSchwartzTest_apply]

theorem coPoissonMuntzTheta_eq_integer_tsum
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (scale_ne : scale ≠ 0) :
    coPoissonMuntzTheta test scale =
      ∑' n : ℤ, test (scale * (n : ℝ)) := by
  have source := summable_integer_evaluation
    (scaledSchwartzTest scale scale_ne test)
  have split := source.sum_add_tsum_subtype_compl ({0} : Finset ℤ)
  let nonzeroEquiv :
      {n : ℤ // n ∉ ({0} : Finset ℤ)} ≃ {n : ℤ // n ≠ 0} := {
    toFun n := ⟨n, by simpa using n.property⟩
    invFun n := ⟨n, by simpa using n.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  have reindex :
      (∑' n : {n : ℤ // n ∉ ({0} : Finset ℤ)},
        test (scale * (n.1 : ℝ))) =
      coPoissonMuntzThetaNonzero test scale := by
    unfold coPoissonMuntzThetaNonzero
    simpa [nonzeroEquiv] using nonzeroEquiv.tsum_eq
      (fun n : {n : ℤ // n ≠ 0} => test (scale * (n.1 : ℝ)))
  have split' :
      test 0 +
          ∑' n : {n : ℤ // n ∉ ({0} : Finset ℤ)},
            test (scale * (n.1 : ℝ)) =
        ∑' n : ℤ, test (scale * (n : ℝ)) := by
    simpa only [Finset.sum_singleton, scaledSchwartzTest_apply,
      mul_zero, Int.cast_zero] using split
  rw [← split', reindex]
  simp [coPoissonMuntzTheta, add_comm]

theorem coPoissonMuntzScaleRemainder_eq
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (positive : 0 < scale) :
    coPoissonMuntzScaleRemainder test scale =
      coPoissonMuntzThetaNonzero test scale -
        (scale⁻¹ : ℝ) • ∫ x : ℝ, test x := by
  rw [coPoissonMuntzScaleRemainder, dif_pos positive,
    clozelTemperedRemainder_apply_nonzero]
  simp only [scaledSchwartzTest_apply]
  have changeVariables := Measure.integral_comp_smul
    (volume : Measure ℝ) (fun x : ℝ => test x) scale
  simp only [Module.finrank_self, pow_one,
    abs_of_pos (inv_pos.mpr positive)] at changeVariables
  exact congrArg (fun value : ℂ =>
    coPoissonMuntzThetaNonzero test scale - value) changeVariables

theorem coPoissonMuntzTheta_fourier_equation
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (positive : 0 < scale) :
    coPoissonMuntzTheta test (1 / scale) =
      (scale : ℂ) • coPoissonMuntzTheta (FourierTransform.fourier test) scale := by
  have inversePositive : 0 < 1 / scale := one_div_pos.mpr positive
  rw [coPoissonMuntzTheta_eq_integer_tsum test inversePositive.ne',
    coPoissonMuntzTheta_eq_integer_tsum (FourierTransform.fourier test)
      positive.ne']
  have poisson := SchwartzMap.tsum_eq_tsum_fourier
    (scaledSchwartzTest (1 / scale) inversePositive.ne' test) 0
  have fourierAtRealZero (n : ℤ) :
      _root_.fourier n ((0 : ℝ) : UnitAddCircle) = 1 := by
    change _root_.fourier n (0 : UnitAddCircle) = 1
    exact _root_.fourier_eval_zero n
  have poisson' :
      (∑' n : ℤ, test (1 / scale * (n : ℝ))) =
        ∑' n : ℤ, FourierTransform.fourier
          (scaledSchwartzTest (1 / scale) inversePositive.ne' test) n := by
    simpa only [zero_add, scaledSchwartzTest_apply,
      fourierAtRealZero, mul_one] using poisson
  have scaledFourier (n : ℤ) :
      FourierTransform.fourier
          (scaledSchwartzTest (1 / scale) inversePositive.ne' test) n =
        (scale : ℂ) * FourierTransform.fourier test (scale * (n : ℝ)) := by
    rw [scaledSchwartzTest_fourier_apply
      (1 / scale) (n : ℝ) inversePositive test]
    norm_num [positive.ne']
    congr 1
    field_simp [positive.ne']
  rw [show (∑' n : ℤ,
      FourierTransform.fourier
        (scaledSchwartzTest (1 / scale) inversePositive.ne' test) n) =
      ∑' n : ℤ, (scale : ℂ) *
        FourierTransform.fourier test (scale * (n : ℝ)) by
    apply tsum_congr
    exact scaledFourier] at poisson'
  rw [tsum_mul_left] at poisson'
  simpa only [one_div, smul_eq_mul] using poisson'

private theorem summable_nonzero_int_norm_pow_inv
    (power : ℕ) (one_lt : 1 < power) :
    Summable (fun n : {n : ℤ // n ≠ 0} =>
      1 / ‖(n.1 : ℝ)‖ ^ power) := by
  have source := Real.summable_abs_int_rpow
    (show (1 : ℝ) < power by exact_mod_cast one_lt)
  refine (source.subtype (fun n : ℤ => n ≠ 0)).congr ?_
  intro n
  have nonnegative : 0 ≤ |(n.1 : ℝ)| := abs_nonneg _
  change |(n.1 : ℝ)| ^ (-(power : ℝ)) =
    1 / ‖(n.1 : ℝ)‖ ^ power
  rw [Real.rpow_neg nonnegative, Real.rpow_natCast]
  simp only [Real.norm_eq_abs, one_div]

private theorem schwartz_scaled_nonzero_bound
    (test : SchwartzMap ℝ ℂ) (power : ℕ)
    {scale : ℝ} (positive : 0 < scale)
    (n : {n : ℤ // n ≠ 0}) :
    ‖test (scale * (n.1 : ℝ))‖ ≤
      (SchwartzMap.seminorm ℝ power 0) test *
        (scale ^ (-(power : ℤ)) *
          (1 / ‖(n.1 : ℝ)‖ ^ power)) := by
  have n_ne : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.property
  have point_ne : scale * (n.1 : ℝ) ≠ 0 :=
    mul_ne_zero positive.ne' n_ne
  have denominator_pos : 0 < ‖scale * (n.1 : ℝ)‖ ^ power :=
    pow_pos (norm_pos_iff.mpr point_ne) _
  have seminormBound := SchwartzMap.norm_pow_mul_le_seminorm
    ℝ test power (scale * (n.1 : ℝ))
  calc
    _ ≤ (SchwartzMap.seminorm ℝ power 0) test /
        ‖scale * (n.1 : ℝ)‖ ^ power := by
      exact (le_div_iff₀ denominator_pos).2 (by
        simpa only [mul_comm] using seminormBound)
    _ = _ := by
      rw [norm_mul, Real.norm_of_nonneg positive.le, mul_pow,
        div_eq_mul_inv]
      simp only [one_div, zpow_neg, zpow_natCast]
      field_simp [positive.ne', norm_ne_zero_iff.mpr n_ne]

private theorem norm_coPoissonMuntzThetaNonzero_le
    (test : SchwartzMap ℝ ℂ) (power : ℕ) (one_lt : 1 < power)
    {scale : ℝ} (positive : 0 < scale) :
    ‖coPoissonMuntzThetaNonzero test scale‖ ≤
      ((SchwartzMap.seminorm ℝ power 0) test *
        ∑' n : {n : ℤ // n ≠ 0}, 1 / ‖(n.1 : ℝ)‖ ^ power) *
          scale ^ (-(power : ℤ)) := by
  let mass : {n : ℤ // n ≠ 0} → ℝ := fun n =>
    1 / ‖(n.1 : ℝ)‖ ^ power
  have massSummable : Summable mass := by
    exact summable_nonzero_int_norm_pow_inv power one_lt
  let bound : {n : ℤ // n ≠ 0} → ℝ := fun n =>
    ((SchwartzMap.seminorm ℝ power 0) test *
      scale ^ (-(power : ℤ))) * mass n
  have boundSummable : Summable bound := massSummable.mul_left _
  have normSummable : Summable (fun n : {n : ℤ // n ≠ 0} =>
      ‖test (scale * (n.1 : ℝ))‖) :=
    boundSummable.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
      dsimp only [bound, mass]
      have source := schwartz_scaled_nonzero_bound
        test power positive n
      nlinarith [source]
  calc
    _ ≤ ∑' n : {n : ℤ // n ≠ 0},
        ‖test (scale * (n.1 : ℝ))‖ := by
      exact norm_tsum_le_tsum_norm normSummable
    _ ≤ ∑' n : {n : ℤ // n ≠ 0}, bound n :=
      normSummable.tsum_le_tsum (fun n => by
        dsimp only [bound, mass]
        have source := schwartz_scaled_nonzero_bound
          test power positive n
        nlinarith [source]) boundSummable
    _ = _ := by
      rw [massSummable.tsum_mul_left]
      dsimp only [mass]
      ring

theorem coPoissonMuntzThetaNonzero_isBigO_atTop
    (test : SchwartzMap ℝ ℂ) (exponent : ℝ) :
    coPoissonMuntzThetaNonzero test =O[atTop]
      (fun scale : ℝ => scale ^ exponent) := by
  let power : ℕ := ⌈-exponent⌉₊ + 2
  have one_lt : 1 < power := by
    dsimp only [power]
    omega
  have exponentComparison : -(power : ℝ) ≤ exponent := by
    have ceilBound := Nat.le_ceil (-exponent)
    dsimp only [power]
    push_cast
    linarith
  let constant : ℝ :=
    (SchwartzMap.seminorm ℝ power 0) test *
      ∑' n : {n : ℤ // n ≠ 0}, 1 / ‖(n.1 : ℝ)‖ ^ power
  have constantNonnegative : 0 ≤ constant := by
    exact mul_nonneg (apply_nonneg _ _)
      (tsum_nonneg fun _ => by positivity)
  refine IsBigO.of_bound constant ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with scale scale_ge
  have positive : 0 < scale := one_pos.trans_le scale_ge
  have source := norm_coPoissonMuntzThetaNonzero_le
    test power one_lt positive
  have powerComparison :
      scale ^ (-(power : ℤ)) ≤ scale ^ exponent := by
    rw [← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le scale_ge
      (by simpa using exponentComparison)
  calc
    ‖coPoissonMuntzThetaNonzero test scale‖ ≤
        constant * scale ^ (-(power : ℤ)) := by
      simpa only [constant] using source
    _ ≤ constant * scale ^ exponent :=
      mul_le_mul_of_nonneg_left powerComparison constantNonnegative
    _ = constant * ‖scale ^ exponent‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg positive.le _)]


end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
