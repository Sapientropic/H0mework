import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ResponseCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ResponseCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace ENNReal
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

/-- The complete original finite dual source converges strongly; no limit or regularity is supplied by a caller. -/
theorem finite_tendsto (side : Bool) : Tendsto (finite side) atTop (𝓝 (value side)) := by
  let majorant : ℝ → ℝ := (symmetricInterval q).indicator (fun _ => (2 * bound side) ^ 2)
  have integrable : Integrable majorant := by
    apply (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr
    exact continuous_const.integrableOn_Icc
  have measured : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable
      (fun x : ℝ => ‖finite side N x - eventRaw side x‖ ^ 2) volume :=
    Eventually.of_forall (fun N => ((Lp.aestronglyMeasurable (finite side N)).sub
      (event_aestronglyMeasurable side)).norm.pow 2)
  have dominated : ∀ᶠ N : ℕ in atTop, ∀ᵐ x : ℝ ∂volume,
      ‖‖finite side N x - eventRaw side x‖ ^ 2‖ ≤ majorant x := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    filter_upwards [finite_coeFn side N, volume.ae_ne (0 : ℝ)] with x read nonzero
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), read]
    dsimp only [majorant]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_mem inside]
      have difference : ‖raw side N x - eventRaw side x‖ ≤ 2 * bound side :=
        (norm_sub_le _ _).trans ((add_le_add (raw_bound side N positive x nonzero)
          (event_bound side x)).trans_eq (by ring))
      exact pow_le_pow_left₀ (norm_nonneg _) difference 2
    · have outside : q < |x| := lt_of_not_ge (fun small => inside (abs_le.mp small))
      rw [indicator_of_notMem inside, raw_outside side N positive x outside,
        event_outside side x outside, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have reads : ∀ᵐ x : ℝ ∂volume, ∀ N : ℕ, finite side N x = raw side N x :=
    ae_all_iff.mpr (finite_coeFn side)
  have pointwise : ∀ᵐ x : ℝ ∂volume, Tendsto
      (fun N : ℕ => ‖finite side N x - eventRaw side x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [reads, volume.ae_ne (0 : ℝ)] with x read nonzero
    apply tendsto_const_nhds.congr'
    filter_upwards [raw_eventually side x nonzero] with N complete
    simp only [read N, complete, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have integralLimit := tendsto_integral_filter_of_dominated_convergence majorant measured dominated integrable pointwise
  simp only [integral_zero] at integralLimit
  have rootLimit := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp integralLimit
  simp only [Real.sqrt_zero] at rootLimit
  have normLimit := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp rootLimit
  simp only [ENNReal.ofReal_zero] at normLimit
  apply Lp.tendsto_Lp_of_tendsto_eLpNorm (eventRaw side) (event_memLp_two side)
  apply normLimit.congr'
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_apply]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ((Lp.memLp (finite side N)).sub (event_memLp_two side))]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply, Real.sqrt_eq_rpow, one_div]

theorem value_mean (side : Bool) :
    burnolQuarterMeanCoefficient (burnolQuarterRestriction (value side)) =
      2 * inner ℂ SmallScaleLog.logL2 (ResponseProfile.state side : BurnolQuarterIntervalL2) := by
  have continuousMean : Continuous (fun value : BurnolL2 =>
      burnolQuarterMeanCoefficient (burnolQuarterRestriction value)) := by
    unfold burnolQuarterMeanCoefficient
    fun_prop
  have actual := (continuousMean.tendsto (value side)).comp (finite_tendsto side)
  have constantRead := actual.congr' (show _ =ᶠ[atTop]
      (fun _ : ℕ => 2 * inner ℂ SmallScaleLog.logL2 (ResponseProfile.state side : BurnolQuarterIntervalL2)) from by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N positive
    exact finite_mean side N positive)
  exact tendsto_nhds_unique constantRead tendsto_const_nhds

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ResponseCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
