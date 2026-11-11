import H0mework.Versions.R7e4da746.Arithmetic.SonineProjection.ConstructorCompact

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ProlateReturn
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal ContDiff Topology
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

private theorem source_moment_integrable (coordinate : BurnolCompletedMellinCoordinate) (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ n *
      ‖(burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x‖) μq := by
  have source := (Lp.memLp (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  apply (source.norm.const_mul (q ^ n)).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval q)] with x hx
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) n) (norm_nonneg _))]
  have bounded : ‖x‖ ≤ q := by simpa only [symmetricInterval, mem_Icc, Real.norm_eq_abs, abs_le] using hx
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) bounded n) (norm_nonneg _)

/-- The original inverse source supplies every finite Fourier moment; no regularity of b is assumed. -/
theorem original_return_contDiff (coordinate : BurnolCompletedMellinCoordinate) :
    ContDiff ℝ ∞ (burnolRieszReturnRaw coordinate) := by
  have source := VectorFourier.contDiff_fourierIntegral (innerSL ℝ) (N := ⊤)
    (fun n _ => source_moment_integrable coordinate n)
  unfold burnolRieszReturnRaw burnolMeanZeroFourierRaw burnolRadiusTruncatedFourierRaw
  have bilinear : (innerₗ ℝ) = (innerSL ℝ).toLinearMap₁₂ := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp only [innerₗ_apply_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply]
  rw [bilinear]
  exact source.sub contDiff_const

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ProlateReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
