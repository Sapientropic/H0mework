import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.FiniteForcing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.FiniteSourceContinuity

open Complex Filter MeasureTheory Set
open scoped Topology
noncomputable section

private theorem normalization_continuous (upper : ℝ) : Continuous (ContinuousChannels.normalization upper) := by
  apply continuous_iff_continuousAt.mpr
  intro value
  let M := ‖value‖ + 1
  have bounded : ∀ᶠ state : BurnolL2 in 𝓝 value, ‖state‖ < M :=
    (tendsto_order.1 (continuous_norm.tendsto value)).2 M (by dsimp [M]; linarith)
  let bound : ℝ → ℝ := fun radius => radius ^ (-(1 / 2 : ℝ)) * M
  have boundIntegral : IntegrableOn bound (Ioc 0 upper) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := upper)
      (by norm_num : -1 < -(1 / 2 : ℝ))).1).mul_const M
  have measured : ∀ᶠ state : BurnolL2 in 𝓝 value,
      AEStronglyMeasurable (fun radius : ℝ => ContinuousChannels.channel (-1) radius state)
        (volume.restrict (Ioc 0 upper)) :=
    Eventually.of_forall (fun state =>
      (ContinuousChannels.channel_integrable (-1) upper state).aestronglyMeasurable)
  have dominated : ∀ᶠ state : BurnolL2 in 𝓝 value, ∀ᵐ radius ∂volume.restrict (Ioc 0 upper),
      ‖ContinuousChannels.channel (-1) radius state‖ ≤ bound radius := by
    filter_upwards [bounded] with state boundState
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    simp only [ContinuousChannels.channel, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg radius), LinearIsometryEquiv.norm_map]
    dsimp only [bound]
    rw [Real.rpow_neg inside.1.le, ← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left boundState.le (inv_nonneg.mpr (Real.sqrt_nonneg radius))
  have pointwise : ∀ᵐ radius ∂volume.restrict (Ioc 0 upper),
      Tendsto (fun state : BurnolL2 => ContinuousChannels.channel (-1) radius state) (𝓝 value)
        (𝓝 (ContinuousChannels.channel (-1) radius value)) := by
    filter_upwards with radius
    exact ((burnolMultiplicativeDilation (-1 * Real.log radius)).continuous.const_smul
      ((Real.sqrt radius : ℂ)⁻¹)).tendsto value
  exact tendsto_integral_filter_of_dominated_convergence bound measured dominated boundIntegral pointwise

/-- Continuity of the actual finite normalized operator permits the original seed's source limit. -/
theorem source_continuous (N : ℕ) : Continuous (FiniteForcing.source N) := by
  unfold FiniteForcing.source
  apply Continuous.sub _ (normalization_continuous N)
  apply continuous_finsetSum
  intro n _
  exact (burnolMultiplicativeDilation (-Real.log (n : ℝ))).continuous.const_smul
    ((Real.sqrt (n : ℝ) : ℂ)⁻¹)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.FiniteSourceContinuity
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
