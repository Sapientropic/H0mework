import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.Mass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual compact co-Poisson inventory transposes against each integrable L² response with its full source normalization. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

private def sourceTerm (source : burnolCompactAnnulusSource) (n : ℕ) (x : ℝ) : ℂ :=
  ((n + 1 : ℕ) : ℂ)⁻¹ * burnolCompactAdditiveSource source (x / (n + 1 : ℕ))

private theorem sourceTerm_outside (source : burnolCompactAnnulusSource) (x : ℝ)
    {n : ℕ} (outside : n ∉ Finset.range ⌊4 * |x|⌋₊) :
    sourceTerm source n x = 0 := by
  have above : 4 * |x| < (n + 1 : ℕ) := by
    have bound := Nat.lt_floor_add_one (4 * |x|)
    have index : ⌊4 * |x|⌋₊ ≤ n := by simpa using outside
    have cast : (⌊4 * |x|⌋₊ : ℝ) ≤ n := by exact_mod_cast index
    push_cast
    linarith
  unfold sourceTerm
  rw [burnolCompactAdditiveSource_zero_of_abs_le_quarter]
  · exact mul_zero _
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < (n + 1 : ℕ) by positivity),
      div_le_iff₀ (show (0 : ℝ) < (n + 1 : ℕ) by positivity)]
    linarith

private theorem sourceTerm_norm_le (source : burnolCompactAnnulusSource) (n : ℕ)
    {x : ℝ} (nonzero : x ≠ 0) :
    ‖sourceTerm source n x‖ ≤
      |x|⁻¹ * SchwartzMap.seminorm ℝ 0 0 source.1 := by
  have positive : 0 < |x| := abs_pos.mpr nonzero
  have absolute : sourceTerm source n x = sourceTerm source n |x| := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx]
      simp only [sourceTerm, neg_div, burnolCompactAdditiveSource_even]
  rw [absolute]
  change ‖((n + 1 : ℕ) : ℂ)⁻¹ *
    burnolCompactAdditiveSource source (|x| / (n + 1 : ℕ))‖ ≤ _
  rw [burnolCompactAdditiveSource_div_nat source positive n, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg positive.le]
  exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ source.1 _)
    (inv_nonneg.mpr positive.le)

private theorem sourceTerm_norm_summable (source : burnolCompactAnnulusSource) (x : ℝ) :
    Summable (fun n : ℕ => ‖sourceTerm source n x‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range ⌊4 * |x|⌋₊)
  intro n outside
  rw [sourceTerm_outside source x outside, norm_zero]

private theorem sourceTerm_totalNorm_le (source : burnolCompactAnnulusSource) (x : ℝ) :
    (∑' n : ℕ, ‖sourceTerm source n x‖) ≤
      4 * SchwartzMap.seminorm ℝ 0 0 source.1 := by
  rw [tsum_eq_sum (s := Finset.range ⌊4 * |x|⌋₊) (fun n outside => by
    rw [sourceTerm_outside source x outside, norm_zero])]
  by_cases zero : x = 0
  · simp only [zero, abs_zero, mul_zero, Nat.floor_zero, Finset.range_zero, Finset.sum_empty]
    positivity
  · have positive : 0 < |x| := abs_pos.mpr zero
    calc
      _ ≤ ∑ _n ∈ Finset.range ⌊4 * |x|⌋₊,
          |x|⁻¹ * SchwartzMap.seminorm ℝ 0 0 source.1 :=
        Finset.sum_le_sum fun n _ => sourceTerm_norm_le source n zero
      _ = (⌊4 * |x|⌋₊ : ℝ) * (|x|⁻¹ * SchwartzMap.seminorm ℝ 0 0 source.1) := by simp
      _ ≤ (4 * |x|) * (|x|⁻¹ * SchwartzMap.seminorm ℝ 0 0 source.1) := by
        gcongr
        exact Nat.floor_le (by positivity)
      _ = _ := by field_simp

private theorem sourceTerm_measurable (source : burnolCompactAnnulusSource) (n : ℕ) :
    Measurable (sourceTerm source n) := by
  have same : burnolCompactAdditiveSource source = burnolCompactTateReciprocalSchwartz source :=
    funext fun x => (burnolCompactTateReciprocalSchwartz_apply source x).symm
  unfold sourceTerm
  rw [same]
  fun_prop

private theorem compactSource_series (value : BurnolL2) (integrable : Integrable value)
    (source : burnolCompactAnnulusSource) :
    (∫ x : ℝ, value x * burnolCompactAdditiveCoSum source x) =
      (∑' n : ℕ, ∫ x : ℝ, value x * sourceTerm source n x) -
        burnolCompactAdditiveNormalization source * ∫ x : ℝ, value x := by
  have whole := (Lp.memLp value).integrable_mul (burnolCompactAdditiveCoSum_memLp_full source)
  have constant := integrable.mul_const (burnolCompactAdditiveNormalization source)
  have forwardInt : Integrable (fun x : ℝ => value x *
      ∑' n : ℕ, sourceTerm source n x) := by
    apply (whole.add constant).congr
    filter_upwards with x
    change value x * burnolCompactAdditiveCoSum source x +
      value x * burnolCompactAdditiveNormalization source = _
    unfold sourceTerm burnolCompactAdditiveCoSum
    ring
  change (∫ x : ℝ, value x * ((∑' n : ℕ, sourceTerm source n x) -
    burnolCompactAdditiveNormalization source)) = _
  simp_rw [mul_sub]
  rw [integral_sub forwardInt constant, integral_mul_const]
  rw [show (fun x : ℝ => value x * ∑' n : ℕ, sourceTerm source n x) =
      fun x => ∑' n : ℕ, value x * sourceTerm source n x by
    funext x
    exact tsum_mul_left.symm]
  have measurable (n : ℕ) : AEStronglyMeasurable (fun x : ℝ =>
      value x * sourceTerm source n x) volume :=
    (Lp.memLp value).1.mul (sourceTerm_measurable source n).aestronglyMeasurable
  have normMeasurable : AEStronglyMeasurable (fun x : ℝ =>
      ∑' n : ℕ, ‖value x * sourceTerm source n x‖) volume := by
    exact AEStronglyMeasurable.tsum (fun n => (measurable n).norm)
  have normSummable (x : ℝ) : Summable (fun n : ℕ => ‖value x * sourceTerm source n x‖) := by
    simpa only [norm_mul] using (sourceTerm_norm_summable source x).mul_left ‖value x‖
  have normIntegral : Integrable (fun x : ℝ => ∑' n : ℕ, ‖value x * sourceTerm source n x‖) := by
    apply (integrable.norm.mul_const (4 * SchwartzMap.seminorm ℝ 0 0 source.1)).mono' normMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
    simp_rw [norm_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (sourceTerm_totalNorm_le source x) (norm_nonneg _)
  have exchange := hasSum_integral_of_dominated_convergence
    (fun n x => ‖value x * sourceTerm source n x‖) measurable
    (fun _ => Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall normSummable) normIntegral
    (Eventually.of_forall (fun x => ((burnolCompactAdditiveCoSum_summable source x).mul_left
      (value x)).hasSum))
  change HasSum (fun n : ℕ => ∫ x : ℝ, value x * sourceTerm source n x)
    (∫ x : ℝ, ∑' n : ℕ, value x * sourceTerm source n x) at exchange
  rw [← exchange.tsum_eq]
  ring

private theorem sourceTerm_integral (value : BurnolL2) (source : burnolCompactAnnulusSource) (n : ℕ) :
    (∫ x : ℝ, value x * sourceTerm source n x) =
      ∫ x : ℝ, value ((n + 1 : ℕ) * x) * burnolCompactAdditiveSource source x := by
  let count : ℝ := ((n + 1 : ℕ) : ℝ)
  have positive : 0 < count := by dsimp only [count]; positivity
  let f : ℝ → ℂ := fun x => value (count * x) * burnolCompactAdditiveSource source x
  calc
    _ = (count : ℂ)⁻¹ * ∫ x : ℝ, f (count⁻¹ * x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [f, sourceTerm]
      rw [← mul_assoc count, mul_inv_cancel₀ positive.ne', one_mul]
      change value x * (((count : ℂ)⁻¹) * burnolCompactAdditiveSource source (x / count)) =
        (count : ℂ)⁻¹ * (value x * burnolCompactAdditiveSource source (count⁻¹ * x))
      simp only [inv_mul_eq_div]
      ring
    _ = ∫ x : ℝ, f x := by
      rw [Measure.integral_comp_mul_left, inv_inv, abs_of_pos positive, Complex.real_smul,
        ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'), one_mul]
    _ = _ := by simp only [f, count, Nat.cast_add, Nat.cast_one]

private theorem compactSource_transpose (value : BurnolL2) (integrable : Integrable value)
    (source : burnolCompactAnnulusSource) :
    (∫ x : ℝ, value x * burnolCompactAdditiveCoSum source x) =
      (∑' n : ℕ, ∫ x : ℝ, value ((n + 1 : ℕ) * x) *
        burnolCompactAdditiveSource source x) -
        burnolCompactAdditiveNormalization source * ∫ x : ℝ, value x := by
  rw [compactSource_series value integrable source]
  congr 1
  exact tsum_congr (sourceTerm_integral value source)

private theorem starred_integrable (value : BurnolL2) (integrable : Integrable value) :
    Integrable (star value : BurnolL2) := by
  apply (Complex.conjCLE.toContinuousLinearMap.integrable_comp integrable).congr
  exact (Lp.coeFn_star value).symm

private theorem starred_integral (value : BurnolL2) :
    (∫ x : ℝ, (star value : BurnolL2) x) = star (∫ x : ℝ, value x) := by
  rw [integral_congr_ae (Lp.coeFn_star value)]
  change (∫ x : ℝ, starRingEnd ℂ (value x)) = starRingEnd ℂ (∫ x : ℝ, value x)
  exact integral_conj

theorem burnolCompactSource_inner_transpose (value : BurnolL2) (integrable : Integrable value)
    (source : burnolCompactAnnulusSource) :
    inner ℂ value (burnolCompactAdditiveL2 source) =
      (∑' n : ℕ, ∫ x : ℝ, star (value ((n + 1 : ℕ) * x)) *
        burnolCompactAdditiveSource source x) -
        burnolCompactAdditiveNormalization source * star (∫ x : ℝ, value x) := by
  have paired := compactSource_transpose (star value) (starred_integrable value integrable) source
  have left : inner ℂ value (burnolCompactAdditiveL2 source) =
      ∫ x : ℝ, (star value : BurnolL2) x * burnolCompactAdditiveCoSum source x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star value, burnolCompactAdditiveL2_coeFn source] with x starAt sourceAt
    rw [starAt, sourceAt]
    simp only [RCLike.inner_apply, Pi.star_apply, Complex.star_def]
    ring
  have terms (n : ℕ) :
      (∫ x : ℝ, (star value : BurnolL2) ((n + 1 : ℕ) * x) *
        burnolCompactAdditiveSource source x) =
      ∫ x : ℝ, star (value ((n + 1 : ℕ) * x)) *
        burnolCompactAdditiveSource source x := by
    have nonzero : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (r := ((n + 1 : ℕ) : ℝ)) nonzero
    apply integral_congr_ae
    filter_upwards [qmp.ae (Lp.coeFn_star value)] with x starAt
    simpa only [smul_eq_mul, Pi.star_apply] using
      congrArg (fun z : ℂ => z * burnolCompactAdditiveSource source x) starAt
  rw [left, paired, starred_integral]
  congr 1
  exact tsum_congr terms

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
