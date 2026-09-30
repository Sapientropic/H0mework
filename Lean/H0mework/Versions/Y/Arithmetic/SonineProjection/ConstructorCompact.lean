import H0mework.Versions.Y.Arithmetic.SonineProjection.Ward
import H0mework.Versions.Y.Arithmetic.MellinProjection.Distribution

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Constructor

open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (Measure.restrict (volume : Measure ℝ) (symmetricInterval q))

local instance compactQuarterFiniteMeasure : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

theorem continuous_memLp (raw : ℝ → ℂ) (continuous : Continuous raw) : MemLp raw 2 μq := by
  obtain ⟨bound, bounded⟩ := isCompact_Icc.exists_bound_of_continuousOn continuous.continuousOn
  apply MemLp.of_bound continuous.aestronglyMeasurable bound
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x inside
  exact bounded x inside

def compact (raw : ℝ → ℂ) (continuous : Continuous raw) : BurnolQuarterIntervalL2 :=
  (continuous_memLp raw continuous).toLp raw

theorem compact_read (raw : ℝ → ℂ) (continuous : Continuous raw) :
    (compact raw continuous : ℝ → ℂ) =ᵐ[μq] raw := MemLp.coeFn_toLp _

theorem compact_add (left right : ℝ → ℂ) (hl : Continuous left) (hr : Continuous right) :
    compact (left + right) (hl.add hr) = compact left hl + compact right hr := rfl

theorem compact_sub (left right : ℝ → ℂ) (hl : Continuous left) (hr : Continuous right) :
    compact (left - right) (hl.sub hr) = compact left hl - compact right hr := rfl

theorem compact_smul (scalar : ℂ) (raw : ℝ → ℂ) (continuous : Continuous raw) :
    compact (scalar • raw) (continuous.const_smul scalar) = scalar • compact raw continuous := rfl

theorem compact_one : compact (fun _ : ℝ => (1 : ℂ)) continuous_const = intervalConstant q := by
  apply Lp.ext
  exact (compact_read _ _).trans (intervalConstant_coeFn q).symm

def zeroMean : BurnolQuarterIntervalL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto

theorem zeroMean_read (state : BurnolQuarterIntervalL2) :
    (zeroMean state : BurnolQuarterIntervalL2) =
      state - burnolQuarterMeanCoefficient state • intervalConstant q :=
  burnolMeanZeroProjection_eq_sub_constant state

theorem zeroMean_constant : zeroMean (intervalConstant q) = 0 := by
  apply Subtype.ext
  exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr (Submodule.mem_span_singleton_self _)

theorem mean_integral (state : BurnolQuarterIntervalL2) :
    burnolQuarterMeanCoefficient state = (2 : ℂ) * ∫ x : ℝ, state x ∂μq := by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow, burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q), L2.inner_def]
  have actual : (∫ x : ℝ, inner ℂ (intervalConstant q x) (state x) ∂μq) =
      ∫ x : ℝ, state x ∂μq := by
    apply integral_congr_ae
    filter_upwards [intervalConstant_coeFn q] with x read
    rw [read]
    simp only [RCLike.inner_apply, map_one, mul_one]
  rw [actual]
  norm_num
  ring

theorem mean_zero (state : BurnolQuarterMeanZeroCarrier) :
    burnolQuarterMeanCoefficient (state : BurnolQuarterIntervalL2) = 0 := by
  have orthogonal : inner ℂ (intervalConstant q) (state : BurnolQuarterIntervalL2) = 0 :=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  unfold burnolQuarterMeanCoefficient
  rw [orthogonal, zero_div]

theorem mean_compact (raw : ℝ → ℂ) (continuous : Continuous raw) :
    burnolQuarterMeanCoefficient (compact raw continuous) =
      (2 : ℂ) * ∫ x : ℝ in (-q)..q, raw x := by
  rw [mean_integral]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  exact integral_congr_ae (compact_read raw continuous)

def fourierRaw (raw : ℝ → ℂ) (frequency : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞 μq (innerₗ ℝ) raw frequency

theorem fourierRaw_integral (raw : ℝ → ℂ) (frequency : ℝ) :
    fourierRaw raw frequency = ∫ x : ℝ in (-q)..q, phase frequency x * raw x := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  unfold fourierRaw VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  simp only [innerₗ_apply_apply, Real.inner_apply, Circle.smul_def, smul_eq_mul, phase]
  rw [mul_comm x frequency]

theorem fourierRaw_state (state : BurnolQuarterIntervalL2) :
    fourierRaw state = burnolRadiusTruncatedFourierRaw q state := rfl

theorem truncatedFourier_read (state : BurnolQuarterIntervalL2) :
    (burnolTruncatedFourier state : ℝ → ℂ) =ᵐ[μq] fourierRaw state :=
  (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
    (fourierL2 (burnolQuarterZeroExtension state))).trans
      (ae_restrict_of_ae (burnolRadiusFourierL2_zeroExtension_ae_eq_raw state))

theorem phaseContinuous (frequency : ℝ) : Continuous (phase frequency) := by
  have controls : Continuous (fun x : ℝ => -(frequency * x)) := by fun_prop
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp controls)

theorem phase_symm (left right : ℝ) : phase left right = phase right left := by
  unfold phase
  rw [mul_comm left right]

theorem fourierRaw_congr (left right : ℝ → ℂ) (same : left =ᵐ[μq] right) :
    fourierRaw left = fourierRaw right := by
  funext frequency
  unfold fourierRaw VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards [same] with x read
  rw [read]

private theorem continuous_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (raw : ℝ → E) (continuous : Continuous raw) : Integrable raw μq := by
  simpa only [symmetricInterval] using! continuous.integrableOn_Icc

private theorem moment_integrable (raw : ℝ → ℂ) (continuous : Continuous raw) :
    Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) raw) μq := by
  apply continuous_integrable
  unfold VectorFourier.fourierSMulRight
  fun_prop

def fourierDerivative (raw : ℝ → ℂ) (frequency : ℝ) : ℂ :=
  (VectorFourier.fourierIntegral 𝐞 μq (innerSL ℝ).toLinearMap₁₂
    (VectorFourier.fourierSMulRight (innerSL ℝ) raw) frequency) 1

theorem fourierRaw_hasDerivAt (raw : ℝ → ℂ) (continuous : Continuous raw) (frequency : ℝ) :
    HasDerivAt (fourierRaw raw) (fourierDerivative raw frequency) frequency := by
  have moment : Integrable (fun x : ℝ => ‖x‖ * ‖raw x‖) μq :=
    continuous_integrable _ (by fun_prop)
  have source := VectorFourier.hasFDerivAt_fourierIntegral (innerSL ℝ)
    (continuous_integrable raw continuous) moment frequency
  unfold fourierRaw fourierDerivative
  have bilinear : (innerₗ ℝ) = (innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [innerₗ_apply_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply]
  rw [bilinear]
  exact source.hasDerivAt

theorem fourierRaw_continuous (raw : ℝ → ℂ) (continuous : Continuous raw) :
    Continuous (fourierRaw raw) :=
  continuous_iff_continuousAt.mpr fun frequency => (fourierRaw_hasDerivAt raw continuous frequency).continuousAt

theorem fourierDerivative_continuous (raw : ℝ → ℂ) (continuous : Continuous raw) :
    Continuous (fourierDerivative raw) := by
  unfold fourierDerivative
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply] using
      (continuous_inner : Continuous (fun p : ℝ × ℝ => inner ℝ p.1 p.2)))
    (moment_integrable raw continuous)).clm_apply continuous_const

theorem fourierDerivative_integral (raw : ℝ → ℂ) (continuous : Continuous raw) (frequency : ℝ) :
    fourierDerivative raw frequency =
      ∫ x : ℝ in (-q)..q, phase frequency x * (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * raw x) := by
  unfold fourierDerivative
  rw [Real.fourierIntegral_continuousLinearMap_apply' (moment_integrable raw continuous)]
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  unfold VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with x
  have innerOne : (innerSL ℝ) x 1 = x := by
    rw [innerSL_apply_apply, Real.inner_apply, mul_one]
  have innerFrequency : (innerSL ℝ) x frequency = x * frequency := by
    rw [innerSL_apply_apply, Real.inner_apply]
  simp only [VectorFourier.fourierSMulRight_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerOne, innerFrequency,
    Circle.smul_def, smul_eq_mul, phase, real_smul]
  rw [mul_comm x frequency]
  ring

end
end OriginalRieszSource.Constructor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
