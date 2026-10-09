import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.Euler
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! The actual constant gap removes the coordinate singularity from the existing Euler derivative; its bounded multiplier generates an ordinary L² derivative. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

private theorem inverse_temperate {f : ℝ → ℝ} (hf : f.HasTemperateGrowth)
    (lower : ∀ x, 1 ≤ f x) :
    (fun x => (f x)⁻¹).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.comp'
    (g := fun y : ℝ => y⁻¹) (t := Ioi (1 / 2 : ℝ)) ?_
    isOpen_Ioi.uniqueDiffOn (contDiffOn_id.inv ?_) ?_ hf
  · rintro _ ⟨x, rfl⟩
    exact lt_of_lt_of_le (by norm_num) (lower x)
  · intro x hx
    exact ne_of_gt (lt_trans (by norm_num) hx)
  · intro N
    refine ⟨0, ∑ k ∈ Finset.range (N + 1), (k.factorial : ℝ) * 2 ^ (k + 1),
      by positivity, ?_⟩
    intro n hn x hx
    have positive : 0 < x := lt_trans (by norm_num) hx
    change (1 / 2 : ℝ) < x at hx
    have smooth : ContDiffAt ℝ n (fun y : ℝ => y⁻¹) x :=
      contDiffAt_id.inv positive.ne'
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_eq_iteratedDeriv isOpen_Ioi.uniqueDiffOn smooth hx,
      iteratedDeriv_eq_iterate, iter_deriv_inv]
    rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, norm_inv,
      Real.norm_natCast, Real.norm_of_nonneg positive.le, pow_zero, mul_one, one_mul]
    calc
      (n.factorial : ℝ) * (x ^ (n + 1))⁻¹ ≤ (n.factorial : ℝ) * 2 ^ (n + 1) := by
        rw [← inv_pow]
        gcongr
        exact (inv_le_comm₀ positive (by norm_num : (0 : ℝ) < 2)).2 (by norm_num; linarith)
      _ ≤ ∑ k ∈ Finset.range (N + 1), (k.factorial : ℝ) * 2 ^ (k + 1) :=
        Finset.single_le_sum (f := fun k => (k.factorial : ℝ) * 2 ^ (k + 1))
          (fun _ _ => by positivity) (by simp; omega)

private def gapBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

private def gapDenominator (x : ℝ) : ℝ := 64 * x ^ 2 + gapBump x

private theorem gapDenominator_lower (x : ℝ) : 1 ≤ gapDenominator x := by
  by_cases small : |x| ≤ 1 / 8
  · have bump : gapBump x = 1 := gapBump.one_of_mem_closedBall (by
      simpa [Metric.mem_closedBall, Real.dist_eq, gapBump] using small)
    simp only [gapDenominator, bump]
    nlinarith [sq_nonneg x]
  · have big : 1 / 8 < |x| := lt_of_not_ge small
    have square : (1 / 8 : ℝ) ^ 2 ≤ x ^ 2 := by
      nlinarith [sq_abs x, sq_nonneg (|x| - 1 / 8)]
    have bump := gapBump.nonneg (x := x)
    dsimp only [gapDenominator]
    nlinarith

private theorem gapDenominator_temperate : gapDenominator.HasTemperateGrowth := by
  have bump := gapBump.hasCompactSupport.hasTemperateGrowth gapBump.contDiff
  unfold gapDenominator
  fun_prop

private def inverseGapCoordinate (x : ℝ) : ℂ :=
  ((64 * x * (gapDenominator x)⁻¹ : ℝ) : ℂ)

private theorem inverseGapCoordinate_temperate : inverseGapCoordinate.HasTemperateGrowth := by
  have generated := inverse_temperate gapDenominator_temperate gapDenominator_lower
  unfold inverseGapCoordinate
  fun_prop


private theorem inverseGapCoordinate_bound (x : ℝ) :
    ‖inverseGapCoordinate x‖ ≤ 64 := by
  have lower := gapDenominator_lower x
  have positive : 0 < gapDenominator x := by linarith
  rw [inverseGapCoordinate, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_inv, abs_of_pos positive]
  norm_num
  rw [← div_eq_mul_inv, div_le_iff₀ positive]
  by_cases small : |x| ≤ 1
  · nlinarith [abs_nonneg x]
  · have big : 1 < |x| := lt_of_not_ge small
    have bump := gapBump.nonneg (x := x)
    dsimp only [gapDenominator] at *
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]

private theorem inverseGapCoordinate_memLp :
    MemLp inverseGapCoordinate ⊤ volume :=
  memLp_top_of_bound inverseGapCoordinate_temperate.1.continuous.aestronglyMeasurable
    64 (Eventually.of_forall inverseGapCoordinate_bound)

private def gapRemainder (x : ℝ) : ℂ :=
  ((gapBump x * (gapDenominator x)⁻¹ : ℝ) : ℂ)

private theorem gapRemainder_temperate : gapRemainder.HasTemperateGrowth := by
  have bump := gapBump.hasCompactSupport.hasTemperateGrowth gapBump.contDiff
  have generated := inverse_temperate gapDenominator_temperate gapDenominator_lower
  unfold gapRemainder
  fun_prop

private theorem gapRemainder_support :
    tsupport gapRemainder ⊆ Icc (-1 / 4 : ℝ) (1 / 4) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra outside
  have far : 1 / 4 ≤ |x| := by
    by_contra nearer
    have near : |x| < 1 / 4 := lt_of_not_ge nearer
    exact outside (by constructor <;> linarith [neg_abs_le x, le_abs_self x])
  have bump : gapBump x = 0 := gapBump.zero_of_le_dist (by
    simpa [gapBump, Real.dist_eq] using far)
  exact hx (by simp [gapRemainder, bump])

private theorem coordinate_partition (x : ℝ) :
    (x : ℂ) * inverseGapCoordinate x + gapRemainder x = 1 := by
  have nonzero : gapDenominator x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
    (gapDenominator_lower x))
  have numeric : x * (64 * x * (gapDenominator x)⁻¹) +
      gapBump x * (gapDenominator x)⁻¹ = 1 := by
    field_simp
    simp only [gapDenominator]
    ring
  unfold inverseGapCoordinate gapRemainder
  exact_mod_cast numeric

private theorem local_gap_derivative_zero
    (value : Lp ℂ 2 (volume : Measure ℝ)) (constant : ℂ)
    (gap : ∀ᵐ x ∂volume, x ∈ Icc (-1 / 4 : ℝ) (1 / 4) → value x = constant)
    (test : SchwartzMap ℝ ℂ)
    (supported : tsupport test ⊆ Icc (-1 / 4 : ℝ) (1 / 4)) :
    TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ) test = 0 := by
  rw [TemperedDistribution.derivCLM_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply]
  have read : (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ test) x • value x) =
      ∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ test) x * constant := by
    apply integral_congr_ae
    filter_upwards [gap] with x source
    by_cases inside : x ∈ Icc (-1 / 4 : ℝ) (1 / 4)
    · rw [source inside, smul_eq_mul]
    · have invisible : (SchwartzMap.derivCLM ℂ ℂ test) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx => inside
          (supported (SchwartzMap.tsupport_derivCLM_subset ℂ test hx)))
      simp [invisible]
  rw [read, integral_mul_const]
  have total := integral_eq_zero_of_hasDerivAt_of_integrable
    test.hasDerivAt (SchwartzMap.derivCLM ℂ ℂ test).integrable test.integrable
  change (∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ test) x) = 0 at total
  rw [total]
  simp only [zero_mul, neg_zero]

theorem burnolOrdinaryDerivative_of_eulerGap
    (value euler : Lp ℂ 2 (volume : Measure ℝ)) (constant : ℂ)
    (gap : ∀ᵐ x ∂volume, x ∈ Icc (-1 / 4 : ℝ) (1 / 4) → value x = constant)
    (generated : TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
      (TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ)) =
      (euler : TemperedDistribution ℝ ℂ)) :
    TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ) =
      ((inverseGapCoordinate_memLp.toLp _ • euler : Lp ℂ 2 volume) :
        TemperedDistribution ℝ ℂ) := by
  rw [Lp.toTemperedDistribution_smul_eq inverseGapCoordinate_temperate
    inverseGapCoordinate_memLp]
  ext test
  let divided := SchwartzMap.smulLeftCLM ℂ inverseGapCoordinate test
  let localTest := SchwartzMap.smulLeftCLM ℂ gapRemainder test
  have partition : test =
      SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) divided + localTest := by
    ext x
    simp only [divided, localTest, SchwartzMap.smulLeftCLM_apply
      inverseGapCoordinate_temperate, SchwartzMap.smulLeftCLM_apply
      gapRemainder_temperate, SchwartzMap.smulLeftCLM_apply (by fun_prop :
      (fun x : ℝ => (x : ℂ)).HasTemperateGrowth), add_apply, smul_eq_mul]
    linear_combination -(coordinate_partition x) * test x
  have localZero := local_gap_derivative_zero value constant gap localTest (by
    change tsupport (SchwartzMap.smulLeftCLM ℂ gapRemainder test) ⊆ _
    rw [SchwartzMap.smulLeftCLM_apply gapRemainder_temperate]
    exact (tsupport_smul_subset_left gapRemainder test).trans gapRemainder_support)
  have landed := congrArg (fun T : TemperedDistribution ℝ ℂ => T divided) generated
  rw [TemperedDistribution.smulLeftCLM_apply_apply] at landed
  calc
    TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ) test =
        TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ)
          (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) divided) := by
      conv_lhs => rw [partition, map_add, localZero, add_zero]
    _ = (euler : TemperedDistribution ℝ ℂ) divided := landed
    _ = _ := rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
