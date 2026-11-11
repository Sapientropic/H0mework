import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import H0mework.Arithmetic.SonineProjection.MeanZeroBlock

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped FourierTransform InnerProductSpace Topology

local notation "q" => (1/4 : ℝ)
local notation "μq" => Measure.restrict (volume : Measure ℝ) (symmetricInterval q)
local notation "F₂" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Hq" => BurnolQuarterIntervalL2

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private def exponentialIntegral (f : Hq) (z : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (z*(t:ℂ))*f t ∂μq

private theorem exponentialIntegral_differentiable (f : Hq) :
    Differentiable ℂ (exponentialIntegral f) := by
  intro z
  let C := Real.exp (‖z‖+1)
  let kernel (w : ℂ) (t : ℝ) := Complex.exp (w*(t:ℂ))*f t
  let derivative (w : ℂ) (t : ℝ) := Complex.exp (w*(t:ℂ))*(t:ℂ)*f t
  have small : ∀ᵐ t : ℝ ∂μq, |t| ≤ 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with t ht
    change -(1/4:ℝ) ≤ t ∧ t ≤ 1/4 at ht
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have bound {w : ℂ} (hw : w ∈ Metric.ball z 1) {t : ℝ} (ht : |t| ≤ 1) :
      ‖Complex.exp (w*(t:ℂ))‖ ≤ C := by
    have size : ‖w‖ ≤ ‖z‖+1 := norm_le_norm_add_const_of_dist_le (Metric.mem_ball.mp hw).le
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ‖w*(t:ℂ)‖ := Complex.re_le_norm _
      _ = ‖w‖*|t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖z‖+1 := by nlinarith [mul_nonneg (norm_nonneg w) (sub_nonneg.mpr ht)]
  have integrable : Integrable (f : ℝ → ℂ) μq := (Lp.memLp f).integrable (by norm_num)
  have boundIntegrable : Integrable (fun t : ℝ => C*‖f t‖) μq := integrable.norm.const_mul C
  have measurable (w : ℂ) : AEStronglyMeasurable (kernel w) μq :=
    ((continuous_const.mul Complex.continuous_ofReal).cexp.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  have initial : Integrable (kernel z) μq := by
    apply boundIntegrable.mono' (measurable z)
    filter_upwards [small] with t ht
    rw [show ‖kernel z t‖ = ‖Complex.exp (z*(t:ℂ))‖*‖f t‖ from norm_mul _ _]
    exact mul_le_mul_of_nonneg_right (bound (Metric.mem_ball_self (by norm_num)) ht) (norm_nonneg _)
  have derivativeMeasurable : AEStronglyMeasurable (derivative z) μq :=
    (((continuous_const.mul Complex.continuous_ofReal).cexp.mul Complex.continuous_ofReal).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  have paid := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μq)
    (F := kernel) (F' := derivative) (bound := fun t => C*‖f t‖)
    (Metric.ball_mem_nhds z (by norm_num : (0:ℝ)<1)) (Eventually.of_forall measurable)
    initial derivativeMeasurable (by
      filter_upwards [small] with t ht w hw
      change ‖Complex.exp (w*(t:ℂ))*(t:ℂ)*f t‖ ≤ C*‖f t‖
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (calc
          _ ≤ ‖Complex.exp (w*(t:ℂ))‖*1 := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
          _ ≤ C := by rw [mul_one]; exact bound hw ht)
        (norm_nonneg _)) boundIntegrable
    (Eventually.of_forall fun t w _ => by
      simpa only [kernel, derivative, id_eq, one_mul] using
        (((hasDerivAt_id w).mul_const (t:ℂ)).cexp).mul_const (f t))
  exact paid.2.differentiableAt

private def frequencyPoint (x : ℝ) : ℂ := (-2*(Real.pi:ℂ)*Complex.I)*(x:ℂ)

private theorem real_slice (f : Hq) (x : ℝ) :
    exponentialIntegral f (frequencyPoint x) = burnolTruncatedFourierRaw f x := by
  rw [burnolTruncatedFourierRaw_eq_fourier_zeroExtension, Real.fourier_real_eq_integral_exp_smul,
    exponentialIntegral, ← integral_indicator (measurableSet_symmetricInterval q)]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases inside : t ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, smul_eq_mul]
    have phase : frequencyPoint x*(t:ℂ) = ((-2*Real.pi*t*x : ℝ):ℂ)*Complex.I := by
      unfold frequencyPoint
      push_cast
      ring
    rw [phase]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside, smul_zero]

private theorem constant_fourier (f : Hq) (k : ℂ)
    (localRead : EqOn (burnolTruncatedFourierRaw f) (fun _ => k) (symmetricInterval q)) :
    ∀ x, burnolTruncatedFourierRaw f x = k := by
  have analytic : AnalyticOnNhd ℂ (exponentialIntegral f) univ :=
    (exponentialIntegral_differentiable f).differentiableOn.analyticOnNhd isOpen_univ
  have nearZero : (0:ℂ) ∈ closure (frequencyPoint '' Ioo 0 q) := by
    have continuous : Continuous frequencyPoint := continuous_const.mul Complex.continuous_ofReal
    have zeroIn : (0:ℝ) ∈ closure (Ioo 0 q) := by
      rw [closure_Ioo (by norm_num : (0:ℝ) ≠ q)]
      exact ⟨le_rfl, by norm_num⟩
    exact image_closure_subset_closure_image continuous ⟨0,zeroIn,by simp [frequencyPoint]⟩
  have still : (0:ℂ) ∈ closure ({z | exponentialIntegral f z = k} \ {0}) := by
    apply closure_mono _ nearZero
    rintro _ ⟨t, inside, rfl⟩
    refine ⟨(real_slice f t).trans (localRead ⟨by linarith [inside.1], inside.2.le⟩), ?_⟩
    exact fun gone => mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt inside.1)) gone
  intro x
  rw [← real_slice]
  exact analytic.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const isPreconnected_univ
    (mem_univ 0) still (mem_univ _)

private theorem centered_fourier_zero_head (z : BurnolQuarterMeanZeroCarrier) :
    burnolTruncatedFourierRaw (z : Hq) 0 = 0 := by
  have head := real_slice (z : Hq) 0
  rw [frequencyPoint, Complex.ofReal_zero, mul_zero, exponentialIntegral] at head
  simp only [zero_mul, Complex.exp_zero, one_mul] at head
  have orthogonal : inner ℂ (intervalConstant q) (z : Hq) = 0 :=
    z.property _ (Submodule.mem_span_singleton_self _)
  rw [L2.inner_def] at orthogonal
  have same : (∫ t : ℝ, (z : Hq) t ∂μq) =
      ∫ t : ℝ, inner ℂ (intervalConstant q t) ((z : Hq) t) ∂μq := by
    apply integral_congr_ae
    filter_upwards [intervalConstant_coeFn q] with t ht
    simp only [ht, RCLike.inner_apply, map_one, mul_one]
  exact head.symm.trans (same.trans orthogonal)

/-- A centered compact quarter source whose true Fourier image has the original position gap is zero. -/
theorem centered_fourier_gap_zero (z : BurnolQuarterMeanZeroCarrier)
    (gap : F₂ (E (z : Hq)) ∈ locallyConstantFace q) : z = 0 := by
  obtain ⟨constant, restrict⟩ := mem_locallyConstantFace_iff_exists.mp gap
  let image := F₂ (E (z : Hq))
  change constant • intervalConstant q = Rq image at restrict
  have raw := burnolFourierL2_zeroExtension_ae_eq_raw (z : Hq)
  have localRead : burnolTruncatedFourierRaw (z : Hq) =ᵐ[μq] fun _ => constant := by
    filter_upwards [ae_restrict_of_ae (s := symmetricInterval q) raw,
      LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q) image,
      Lp.coeFn_smul constant (intervalConstant q), intervalConstant_coeFn q]
      with t hraw hrestrict hscale hone
    change image t = _ at hraw
    change Rq image t = image t at hrestrict
    rw [← hraw, ← hrestrict, ← restrict, hscale]
    change constant * intervalConstant q t = constant
    rw [hone, mul_one]
  have localPointwise : EqOn (burnolTruncatedFourierRaw (z : Hq)) (fun _ => constant)
      (symmetricInterval q) :=
    Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) (by norm_num : -q ≠ q) localRead
      (burnolRadiusTruncatedFourierRaw_continuous _).continuousOn continuous_const.continuousOn
  have full := constant_fourier (z : Hq) constant localPointwise
  have zero : constant = 0 := (full 0).symm.trans (centered_fourier_zero_head z)
  have erased : image = 0 := by
    apply Lp.ext
    filter_upwards [raw, Lp.coeFn_zero ℂ 2 volume] with t read value
    exact read.trans ((full t).trans (zero.trans value.symm))
  have stored := congrArg Rq ((F₂).injective (erased.trans (map_zero (F₂)).symm))
  rw [burnolQuarterRestriction_zeroExtension, map_zero] at stored
  exact Subtype.ext stored

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
