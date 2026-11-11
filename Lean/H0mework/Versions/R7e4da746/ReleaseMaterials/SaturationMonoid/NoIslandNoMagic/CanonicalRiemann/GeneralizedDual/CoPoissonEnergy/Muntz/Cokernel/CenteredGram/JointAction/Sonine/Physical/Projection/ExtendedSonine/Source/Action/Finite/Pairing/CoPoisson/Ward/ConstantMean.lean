import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantForward

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ConstantMean

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

theorem log_pair : inner ℂ SmallScaleLog.logL2 (intervalConstant q) = -(1 / 2 : ℂ) := by
  rw [L2.inner_def]
  have raw : (fun x : ℝ => inner ℂ (SmallScaleLog.logL2 x) (intervalConstant q x)) =ᵐ[μq]
      fun x => ((Real.log x - Real.log q : ℝ) : ℂ) := by
    filter_upwards [SmallScaleLog.log_coeFn, intervalConstant_coeFn q,
      ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))] with x log constant nonzero
    rw [log, constant, SmallScaleLog.logRaw, RCLike.inner_apply]
    simp only [one_mul, starRingEnd_apply]
    rw [star_def, Complex.conj_ofReal,
      Real.log_div (abs_ne_zero.mpr nonzero) (by norm_num : q ≠ 0), Real.log_abs]
  rw [integral_congr_ae raw, integral_complex_ofReal]
  have integral : (∫ x : ℝ, Real.log x - Real.log q ∂μq) = -(1 / 2 : ℝ) := by
    change (∫ x : ℝ in Icc (-q) q, Real.log x - Real.log q) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
      intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log' (intervalIntegrable_const),
      integral_log, intervalIntegral.integral_const, Real.log_neg_eq_log]
    norm_num [smul_eq_mul]
    ring
  rw [integral]
  norm_num

theorem forward_window : burnolQuarterRestriction ConstantForward.value =
    (Real.eulerMascheroniConstant : ℂ) • intervalConstant q + SmallScaleLog.logL2 := by
  have source := (burnolQuarterRestriction.continuous.tendsto ConstantForward.value).comp ConstantForward.original_tendsto
  exact tendsto_nhds_unique source WindowCounting.constant_limit

/-- The complete finite adjoint reads the actual nonzero mean of H. -/
theorem original_pair : inner ℂ ConstantDual.seed ConstantDual.value =
    (1 / 2 : ℂ) * (Real.eulerMascheroniConstant - 1) := by
  have forward := ConstantForward.original_tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := ConstantDual.seed))
  have reverse := (tendsto_const_nhds (x := ConstantDual.seed)).inner (𝕜 := ℂ) ConstantDual.original_tendsto
  have same := forward.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N _ _))
  have adjoint := tendsto_nhds_unique same reverse
  have restriction : inner ℂ ConstantForward.value ConstantDual.seed =
      inner ℂ (burnolQuarterRestriction ConstantForward.value) (intervalConstant q) :=
    ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
  have square : inner ℂ (intervalConstant q) (intervalConstant q) = (1 / 2 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖intervalConstant q‖ : ℂ) ^ 2 = (1 / 2 : ℂ)
    convert! burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q) using 1
    norm_num
  rw [← adjoint, restriction, forward_window, inner_add_left, inner_smul_left, square, log_pair]
  simp only [Complex.conj_ofReal]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ConstantMean
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
