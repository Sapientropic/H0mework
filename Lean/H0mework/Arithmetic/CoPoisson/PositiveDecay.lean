import H0mework.Arithmetic.CoPoisson.LogOrbit

/-!
# Positive-end decay of the actual co-Poisson log orbit

The nonzero-lattice formula, the quadratic Schwartz seminorm, and scaled
integration give an explicit `O(exp (-x / 2))` bound at `+∞`.  This is a
source theorem for every Schwartz test; it assumes no zero, contact, or
criticality statement.
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

open Complex FourierTransform MeasureTheory Filter
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace Topology

noncomputable section

private theorem summable_nonzero_int_square :
    Summable (fun n : {n : ℤ // n ≠ 0} => 1 / ‖(n.1 : ℝ)‖ ^ 2) := by
  have source : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine (source.subtype (fun n : ℤ => n ≠ 0)).congr ?_
  intro n
  simp only [Function.comp_apply, Real.norm_eq_abs, sq_abs]

private def nonzeroIntSquareMass : ℝ :=
  ∑' n : {n : ℤ // n ≠ 0}, 1 / ‖(n.1 : ℝ)‖ ^ 2

private theorem nonzeroIntSquareMass_nonneg : 0 ≤ nonzeroIntSquareMass :=
  tsum_nonneg fun _ => by positivity

private theorem schwartz_nonzero_scaled_bound
    (test : SchwartzMap ℝ ℂ) (x : ℝ) (n : {n : ℤ // n ≠ 0}) :
    ‖test (Real.exp x * (n.1 : ℝ))‖ ≤
      (SchwartzMap.seminorm ℝ 2 0) test *
        (Real.exp (-2 * x) * (1 / ‖(n.1 : ℝ)‖ ^ 2)) := by
  have hn0 : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.property
  have hz0 : Real.exp x * (n.1 : ℝ) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero x) hn0
  have hden : 0 < ‖Real.exp x * (n.1 : ℝ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hz0) _
  have hsemi := SchwartzMap.norm_pow_mul_le_seminorm ℝ test 2
    (Real.exp x * (n.1 : ℝ))
  calc
    ‖test (Real.exp x * (n.1 : ℝ))‖ ≤
        (SchwartzMap.seminorm ℝ 2 0) test /
          ‖Real.exp x * (n.1 : ℝ)‖ ^ 2 := by
      apply (le_div_iff₀ hden).2
      simpa only [mul_comm] using hsemi
    _ = _ := by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos x).le, mul_pow]
      rw [show -2 * x = -(2 * x) by ring, Real.exp_neg,
        show Real.exp (2 * x) = Real.exp x ^ 2 by
          simpa using Real.exp_nat_mul x 2]
      field_simp [Real.exp_ne_zero x, norm_ne_zero_iff.mpr hn0]

private theorem norm_tsum_schwartz_nonzero_scaled_le
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖∑' n : {n : ℤ // n ≠ 0}, test (Real.exp x * (n.1 : ℝ))‖ ≤
      (SchwartzMap.seminorm ℝ 2 0) test * Real.exp (-2 * x) *
        nonzeroIntSquareMass := by
  let bound : {n : ℤ // n ≠ 0} → ℝ := fun n =>
    ((SchwartzMap.seminorm ℝ 2 0) test * Real.exp (-2 * x)) *
      (1 / ‖(n.1 : ℝ)‖ ^ 2)
  have hbound : Summable bound := summable_nonzero_int_square.mul_left _
  have hnorm : Summable (fun n : {n : ℤ // n ≠ 0} =>
      ‖test (Real.exp x * (n.1 : ℝ))‖) :=
    hbound.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => by
      simpa only [bound, mul_assoc] using schwartz_nonzero_scaled_bound test x n
  calc
    ‖∑' n : {n : ℤ // n ≠ 0}, test (Real.exp x * (n.1 : ℝ))‖ ≤
        ∑' n : {n : ℤ // n ≠ 0}, ‖test (Real.exp x * (n.1 : ℝ))‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : {n : ℤ // n ≠ 0}, bound n :=
      hnorm.tsum_le_tsum (fun n => by
        simpa only [bound, mul_assoc] using
          schwartz_nonzero_scaled_bound test x n) hbound
    _ = _ := by
      rw [show (∑' n : {n : ℤ // n ≠ 0}, bound n) =
          ((SchwartzMap.seminorm ℝ 2 0) test * Real.exp (-2 * x)) *
            ∑' n : {n : ℤ // n ≠ 0}, 1 / ‖(n.1 : ℝ)‖ ^ 2 by
        exact summable_nonzero_int_square.tsum_mul_left _]
      rfl

private theorem integral_scaledSchwartzTest_exp
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    (∫ y : ℝ, scaledSchwartzTest (Real.exp x) (Real.exp_ne_zero x) test y) =
      Real.exp (-x) • ∫ y : ℝ, test y := by
  have source := Measure.integral_comp_smul
    (volume : Measure ℝ) (fun y : ℝ => test y) (Real.exp x)
  simp only [Module.finrank_self, pow_one] at source
  rw [abs_of_pos (inv_pos.mpr (Real.exp_pos x)), ← Real.exp_neg] at source
  simpa only [scaledSchwartzTest_apply, smul_eq_mul, Module.finrank_self,
    pow_one] using source

theorem coPoissonLogOrbitMap_nonzero_formula
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    coPoissonLogOrbitMap test x =
      (Real.exp x : ℂ) ^ (1 / 2 : ℂ) *
        ((∑' n : {n : ℤ // n ≠ 0}, test (Real.exp x * (n.1 : ℝ))) -
          Real.exp (-x) • ∫ y : ℝ, test y) := by
  change (Real.exp x : ℂ) ^ (1 / 2 : ℂ) *
    clozelTemperedRemainder
      (scaledSchwartzTest (Real.exp x) (Real.exp_ne_zero x) test) = _
  rw [clozelTemperedRemainder_apply_nonzero]
  simp only [scaledSchwartzTest_apply]
  have integralEq : (∫ y : ℝ, test (Real.exp x * y)) =
      Real.exp (-x) • ∫ y : ℝ, test y := by
    simpa only [scaledSchwartzTest_apply] using
      integral_scaledSchwartzTest_exp test x
  rw [integralEq]

private theorem norm_exp_cpow_half (x : ℝ) :
    ‖(Real.exp x : ℂ) ^ (1 / 2 : ℂ)‖ = Real.exp (x / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos x)]
  norm_num
  rw [← Real.exp_mul]
  congr 1
  ring

def coPoissonPositiveBound (test : SchwartzMap ℝ ℂ) : ℝ :=
  (SchwartzMap.seminorm ℝ 2 0) test * nonzeroIntSquareMass +
    ‖∫ y : ℝ, test y‖

theorem coPoissonPositiveBound_nonneg (test : SchwartzMap ℝ ℂ) :
    0 ≤ coPoissonPositiveBound test := by
  exact add_nonneg
    (mul_nonneg (apply_nonneg _ _) nonzeroIntSquareMass_nonneg)
    (norm_nonneg _)

theorem coPoissonLogOrbitMap_norm_le_positive
    (test : SchwartzMap ℝ ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖coPoissonLogOrbitMap test x‖ ≤
      coPoissonPositiveBound test * Real.exp (-x / 2) := by
  rw [coPoissonLogOrbitMap_nonzero_formula, norm_mul, norm_exp_cpow_half]
  have hsum : ‖∑' n : {n : ℤ // n ≠ 0},
      test (Real.exp x * (n.1 : ℝ))‖ ≤
      ((SchwartzMap.seminorm ℝ 2 0) test * nonzeroIntSquareMass) *
        Real.exp (-x) := by
    calc
      _ ≤ (SchwartzMap.seminorm ℝ 2 0) test * Real.exp (-2 * x) *
          nonzeroIntSquareMass := norm_tsum_schwartz_nonzero_scaled_le test x
      _ = ((SchwartzMap.seminorm ℝ 2 0) test * nonzeroIntSquareMass) *
          Real.exp (-2 * x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (mul_nonneg (apply_nonneg _ _) nonzeroIntSquareMass_nonneg)
  have hintegral : ‖Real.exp (-x) • ∫ y : ℝ, test y‖ =
      Real.exp (-x) * ‖∫ y : ℝ, test y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-x))]
  have hexp : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (x / 2) * ‖(∑' n : {n : ℤ // n ≠ 0},
        test (Real.exp x * (n.1 : ℝ))) -
        Real.exp (-x) • ∫ y : ℝ, test y‖ ≤
      Real.exp (x / 2) * (‖∑' n : {n : ℤ // n ≠ 0},
        test (Real.exp x * (n.1 : ℝ))‖ +
        ‖Real.exp (-x) • ∫ y : ℝ, test y‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ Real.exp (x / 2) *
        (((SchwartzMap.seminorm ℝ 2 0) test * nonzeroIntSquareMass) *
          Real.exp (-x) + Real.exp (-x) * ‖∫ y : ℝ, test y‖) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact add_le_add hsum (le_of_eq hintegral)
    _ = _ := by
      unfold coPoissonPositiveBound
      rw [← hexp]
      ring

theorem coPoissonLogOrbitMap_norm_tendsto_atTop
    (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun x : ℝ => ‖coPoissonLogOrbitMap test x‖) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun x : ℝ => Real.exp (-x / 2)) atTop (𝓝 0) := by
    have source := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1 / 2 : ℝ) < 0))
    convert source using 1
    funext x
    simp only [Function.comp_apply, id_eq]
    congr 1
    ring
  have hdom : Tendsto (fun x : ℝ =>
      coPoissonPositiveBound test * Real.exp (-x / 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
    ?_ hdom
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact coPoissonLogOrbitMap_norm_le_positive test hx

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
