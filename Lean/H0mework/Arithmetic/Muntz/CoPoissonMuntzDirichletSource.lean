import H0mework.Arithmetic.Tempered.MuntzTheta

/-!
# Even source Mellin factor and positive-integer theta expansion

The two signs of every nonzero lattice point are assembled into an even
Schwartz source.  Its Mellin transform converges and is analytic on the
positive half-plane; exact norm scaling supplies the Tonelli majorant used
by the Dirichlet seed.
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

def coPoissonMuntzEvenSource
    (test : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  test t + test (-t)

def coPoissonMuntzEvenSourceMellin
    (test : SchwartzMap ℝ ℂ) (s : ℂ) : ℂ :=
  mellin (coPoissonMuntzEvenSource test) s

theorem coPoissonMuntzThetaNonzero_eq_positive_tsum
    (test : SchwartzMap ℝ ℂ) {scale : ℝ} (scale_ne : scale ≠ 0) :
    coPoissonMuntzThetaNonzero test scale =
      ∑' n : ℕ, coPoissonMuntzEvenSource test
        ((n + 1 : ℕ) * scale) := by
  let summand : ℤ → ℂ := fun n => test (scale * (n : ℝ))
  have fullSummable : Summable summand := by
    simpa only [summand, scaledSchwartzTest_apply] using
      summable_integer_evaluation
        (scaledSchwartzTest scale scale_ne test)
  have positiveSummable : Summable (fun n : ℕ => summand n) :=
    fullSummable.comp_injective Nat.cast_injective
  have negativeSummable : Summable
      (fun n : ℕ => summand (-(n + 1))) :=
    fullSummable.comp_injective (@Int.negSucc.inj)
  have positiveTailSummable : Summable
      (fun n : ℕ => summand (n + 1)) :=
    positiveSummable.comp_injective Nat.succ_injective
  have fullSplit := tsum_of_nat_of_neg_add_one
    positiveSummable negativeSummable
  have positiveSplit := positiveSummable.sum_add_tsum_nat_add 1
  have positiveSplit' : test 0 +
      (∑' n : ℕ, summand (n + 1)) =
        ∑' n : ℕ, summand n := by
    simpa [summand] using positiveSplit
  have thetaFull := coPoissonMuntzTheta_eq_integer_tsum test scale_ne
  calc
    coPoissonMuntzThetaNonzero test scale =
        coPoissonMuntzTheta test scale - test 0 := by
      simp [coPoissonMuntzTheta]
    _ = (∑' n : ℤ, summand n) - test 0 := by
      rw [thetaFull]
    _ = ((∑' n : ℕ, summand n) +
          ∑' n : ℕ, summand (-(n + 1))) - test 0 := by
      rw [fullSplit]
    _ = (∑' n : ℕ, summand (n + 1)) +
          ∑' n : ℕ, summand (-(n + 1)) := by
      rw [← positiveSplit']
      ring
    _ = ∑' n : ℕ,
          (summand (n + 1) + summand (-(n + 1))) := by
      exact (positiveTailSummable.tsum_add negativeSummable).symm
    _ = _ := by
      apply tsum_congr
      intro n
      simp only [summand, coPoissonMuntzEvenSource,
        Nat.cast_add, Nat.cast_one]
      congr 2 <;> push_cast <;> ring

private theorem coPoissonMuntzEvenSource_locallyIntegrableOn
    (test : SchwartzMap ℝ ℂ) :
    LocallyIntegrableOn (coPoissonMuntzEvenSource test) (Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (test.continuous.add (test.continuous.comp continuous_neg)).continuousOn

private theorem coPoissonMuntzEvenSource_isBigO_atTop
    (test : SchwartzMap ℝ ℂ) (exponent : ℝ) :
    coPoissonMuntzEvenSource test =O[atTop]
      (fun t : ℝ => t ^ exponent) := by
  have positiveSide :=
    (test.isBigO_cocompact_rpow exponent).mono
      (atTop_le_cocompact : atTop ≤ cocompact ℝ)
  have negativeTendsCocompact : Tendsto (fun t : ℝ => -t)
      atTop (cocompact ℝ) :=
    tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact
  have negativeSide :=
    (test.isBigO_cocompact_rpow exponent).comp_tendsto
      negativeTendsCocompact
  have negativeSide' : (fun t : ℝ => test (-t)) =O[atTop]
      (fun t : ℝ => ‖t‖ ^ exponent) :=
    negativeSide.congr'
      (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun t => by simp)
  have both : coPoissonMuntzEvenSource test =O[atTop]
      (fun t : ℝ => ‖t‖ ^ exponent) := by
    unfold coPoissonMuntzEvenSource
    apply positiveSide.add
    exact negativeSide'
  apply both.trans
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t nonnegative
  simp only [one_mul, Real.norm_eq_abs, abs_of_nonneg nonnegative]
  exact le_rfl

private theorem coPoissonMuntzEvenSource_isBigO_zero
    (test : SchwartzMap ℝ ℂ) :
    coPoissonMuntzEvenSource test =O[
      nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound
    (2 * (SchwartzMap.seminorm ℝ 0 0) test) ?_
  filter_upwards with t
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  unfold coPoissonMuntzEvenSource
  calc
    ‖test t + test (-t)‖ ≤ ‖test t‖ + ‖test (-t)‖ := norm_add_le _ _
    _ ≤ (SchwartzMap.seminorm ℝ 0 0) test +
        (SchwartzMap.seminorm ℝ 0 0) test := by
      exact add_le_add (SchwartzMap.norm_le_seminorm ℝ test t)
        (SchwartzMap.norm_le_seminorm ℝ test (-t))
    _ = _ := by ring

theorem coPoissonMuntzEvenSource_mellinConvergent
    (test : SchwartzMap ℝ ℂ) (s : ℂ) (positive : 0 < s.re) :
    MellinConvergent (coPoissonMuntzEvenSource test) s := by
  exact mellinConvergent_of_isBigO_rpow
    (coPoissonMuntzEvenSource_locallyIntegrableOn test)
    (coPoissonMuntzEvenSource_isBigO_atTop test (-(s.re + 1)))
    (by linarith)
    (coPoissonMuntzEvenSource_isBigO_zero test) positive

theorem coPoissonMuntzEvenSourceMellin_differentiableAt
    (test : SchwartzMap ℝ ℂ) (s : ℂ) (positive : 0 < s.re) :
    DifferentiableAt ℂ (coPoissonMuntzEvenSourceMellin test) s := by
  unfold coPoissonMuntzEvenSourceMellin
  exact mellin_differentiableAt_of_isBigO_rpow
    (coPoissonMuntzEvenSource_locallyIntegrableOn test)
    (coPoissonMuntzEvenSource_isBigO_atTop test (-(s.re + 1)))
    (by linarith)
    (coPoissonMuntzEvenSource_isBigO_zero test) positive

theorem integral_norm_mellin_comp_mul_left
    (f : ℝ → ℂ) (s : ℂ) {scale : ℝ} (scalePositive : 0 < scale) :
    (∫ t : ℝ in Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * f (scale * t)‖) =
      scale ^ (-s.re) *
        ∫ u : ℝ in Ioi 0, ‖(u : ℂ) ^ (s - 1) * f u‖ := by
  let weightedNorm : ℝ → ℝ := fun u =>
    ‖(u : ℂ) ^ (s - 1) * f u‖
  have pointwise (t : ℝ) (positive : t ∈ Ioi (0 : ℝ)) :
      ‖(t : ℂ) ^ (s - 1) * f (scale * t)‖ =
        scale ^ (1 - s.re) * weightedNorm (scale * t) := by
    dsimp only [weightedNorm]
    rw [norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos positive,
      Complex.norm_cpow_eq_rpow_re_of_pos
        (mul_pos scalePositive positive),
      Real.mul_rpow scalePositive.le positive.le]
    have cancellation :
        scale ^ (1 - s.re) * scale ^ (s - 1).re = 1 := by
      rw [← Real.rpow_add scalePositive]
      norm_num [Complex.sub_re]
    calc
      t ^ (s - 1).re * ‖f (scale * t)‖ =
          1 * (t ^ (s - 1).re * ‖f (scale * t)‖) := by ring
      _ = (scale ^ (1 - s.re) * scale ^ (s - 1).re) *
          (t ^ (s - 1).re * ‖f (scale * t)‖) := by rw [cancellation]
      _ = scale ^ (1 - s.re) *
          (scale ^ (s - 1).re * t ^ (s - 1).re *
            ‖f (scale * t)‖) := by ac_rfl
  calc
    _ = ∫ t : ℝ in Ioi 0,
        scale ^ (1 - s.re) * weightedNorm (scale * t) := by
      exact setIntegral_congr_fun measurableSet_Ioi pointwise
    _ = scale ^ (1 - s.re) *
        ∫ t : ℝ in Ioi 0, weightedNorm (scale * t) := by
      rw [integral_const_mul]
    _ = scale ^ (1 - s.re) *
        (scale⁻¹ * ∫ u : ℝ in Ioi 0, weightedNorm u) := by
      rw [integral_comp_mul_left_Ioi weightedNorm 0 scalePositive,
        mul_zero]
      rfl
    _ = scale ^ (-s.re) *
        ∫ u : ℝ in Ioi 0, weightedNorm u := by
      rw [← Real.rpow_neg_one]
      rw [← mul_assoc, ← Real.rpow_add scalePositive]
      congr 2
      ring


end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
