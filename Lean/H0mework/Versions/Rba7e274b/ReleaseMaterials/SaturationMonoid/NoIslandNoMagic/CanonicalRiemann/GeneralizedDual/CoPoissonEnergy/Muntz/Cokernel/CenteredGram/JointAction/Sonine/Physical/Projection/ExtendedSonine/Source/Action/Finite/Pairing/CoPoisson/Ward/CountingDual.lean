import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountingDual

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

private theorem source_add (N : ℕ) (left right : BurnolL2) :
    FiniteForcing.source N (left + right) = FiniteForcing.source N left + FiniteForcing.source N right := by
  unfold FiniteForcing.source ContinuousChannels.normalization
  simp only [Channels.sourceChannel, ContinuousChannels.channel, map_add, smul_add, Finset.sum_add_distrib]
  have sumIntegral := integral_add (ContinuousChannels.channel_integrable (-1) N left)
    (ContinuousChannels.channel_integrable (-1) N right)
  simp only [ContinuousChannels.channel] at sumIntegral
  rw [sumIntegral]
  abel

private theorem source_smul (N : ℕ) (scalar : ℂ) (value : BurnolL2) :
    FiniteForcing.source N (scalar • value) = scalar • FiniteForcing.source N value := by
  have integer (n : ℕ) : Channels.sourceChannel n (scalar • value) = scalar • Channels.sourceChannel n value := by
    simp only [Channels.sourceChannel, map_smul, smul_smul]
    module
  have channel (radius : ℝ) : ContinuousChannels.channel (-1) radius (scalar • value) =
      scalar • ContinuousChannels.channel (-1) radius value := by
    simp only [ContinuousChannels.channel, map_smul, smul_smul]
    module
  unfold FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer, channel, integral_smul, ← Finset.smul_sum]
  exact (smul_sub scalar _ _).symm

/-- The original finite programme supplies its own linearity and strong-integral continuity. -/
def sourceCLM (N : ℕ) : BurnolL2 →L[ℂ] BurnolL2 where
  toFun := FiniteForcing.source N
  map_add' := source_add N
  map_smul' := source_smul N
  cont := FiniteSourceContinuity.source_continuous N

@[simp] theorem sourceCLM_apply (N : ℕ) (value : BurnolL2) : sourceCLM N value = FiniteForcing.source N value := rfl

/-- Both original finite sides retain the same counting cutoff and the entire positive-scale contact. -/
theorem source_pairing (N : ℕ) (left right : BurnolL2) :
    inner ℂ (FiniteForcing.source N left) right = inner ℂ left (DualSource.source N right) := by
  unfold FiniteForcing.source DualSource.source
  rw [inner_sub_left, inner_sub_right, sum_inner, inner_sum]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro n _
    simpa only [Channels.sourceChannel, ContinuousChannels.channel, neg_one_mul, one_mul] using
      ContinuousChannels.channel_pairing n left right
  · exact ContinuousChannels.normalization_pairing N left right

/-- The independently constructed reverse source is recognized as the actual adjoint. -/
theorem dual_eq_adjoint (N : ℕ) (value : BurnolL2) :
    DualSource.source N value = (sourceCLM N).adjoint value := by
  apply ext_inner_left ℂ
  intro test
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (source_pairing N test value).symm

private theorem source_channel (N : ℕ) (direction radius : ℝ) (value : BurnolL2) :
    sourceCLM N (ContinuousChannels.channel direction radius value) =
      ContinuousChannels.channel direction radius (sourceCLM N value) := by
  unfold ContinuousChannels.channel
  rw [map_smul]
  exact congrArg ((Real.sqrt radius : ℂ)⁻¹ • ·)
    (SeedCounting.source_dilation N (direction * Real.log radius) value)

/-- The two finite original counting operators commute by their common dilation action. -/
theorem source_commute (N M : ℕ) : Commute (sourceCLM N) (sourceCLM M) := by
  apply ContinuousLinearMap.ext
  intro value
  change sourceCLM N (FiniteForcing.source M value) = FiniteForcing.source M (sourceCLM N value)
  have original (seed : BurnolL2) : FiniteForcing.source M seed =
      (∑ n ∈ Finset.Ico 1 M, ContinuousChannels.channel (-1) n seed) -
        ∫ radius : ℝ in Ioc 0 (M : ℝ), ContinuousChannels.channel (-1) radius seed := by
    simp only [FiniteForcing.source, ContinuousChannels.normalization, Channels.sourceChannel,
      ContinuousChannels.channel, neg_one_mul]
  rw [original, original, map_sub, map_sum,
    ← (sourceCLM N).integral_comp_comm (ContinuousChannels.channel_integrable (-1) M value)]
  simp_rw [source_channel]

/-- The complete forward and reverse programmes commute; no integral of operators is used. -/
theorem source_dual_commute (N M : ℕ) : Commute (sourceCLM N) (sourceCLM M).adjoint := by
  apply ContinuousLinearMap.ext
  intro value
  change sourceCLM N ((sourceCLM M).adjoint value) = (sourceCLM M).adjoint (sourceCLM N value)
  rw [← dual_eq_adjoint, ← dual_eq_adjoint]
  unfold DualSource.source
  rw [map_sub, map_sum, ← (sourceCLM N).integral_comp_comm (ContinuousChannels.channel_integrable 1 M value)]
  simp_rw [source_channel]

/-- The independent reverse operators inherit their mutual commutation from the same forward source. -/
theorem dual_commute (N M : ℕ) : Commute (sourceCLM N).adjoint (sourceCLM M).adjoint := by
  have source := congrArg ContinuousLinearMap.adjoint (source_commute M N).eq
  change (sourceCLM N).adjoint * (sourceCLM M).adjoint =
    (sourceCLM M).adjoint * (sourceCLM N).adjoint
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp] using source

/-- Normality is generated for every actual difference of finite cutoffs. -/
theorem source_difference_normal (N M : ℕ) : IsStarNormal (sourceCLM N - sourceCLM M) := by
  have same := ((source_dual_commute N N).sub_right (source_dual_commute N M)).sub_left
    ((source_dual_commute M N).sub_right (source_dual_commute M M))
  rw [isStarNormal_iff]
  change Commute ((sourceCLM N - sourceCLM M).adjoint) (sourceCLM N - sourceCLM M)
  rw [map_sub]
  exact same.symm

/-- The full independent dual differences have exactly the original source norms. -/
theorem difference_norm (N M : ℕ) (value : BurnolL2) :
    ‖DualSource.source N value - DualSource.source M value‖ =
      ‖FiniteForcing.source N value - FiniteForcing.source M value‖ := by
  have actual := ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp
    (source_difference_normal N M) value
  simpa only [map_sub, sub_apply, sourceCLM_apply, ← dual_eq_adjoint] using actual.symm

/-- The original ambient source convergence generates Cauchy control of its independent dual. -/
theorem original_dual_cauchy (coordinate : BurnolCompletedMellinCoordinate) :
    CauchySeq (fun N : ℕ => DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) := by
  have actual := (AmbientCounting.original_ambient_limit coordinate).cauchySeq
  rw [Metric.cauchySeq_iff] at actual ⊢
  intro epsilon positive
  obtain ⟨N, after⟩ := actual epsilon positive
  refine ⟨N, ?_⟩
  intro m hm n hn
  simpa only [dist_eq_norm, difference_norm] using after m hm n hn

/-- The canonical limit is taken from this same independently generated dual sequence. -/
def value (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  limUnder atTop (fun N : ℕ => DualSource.source N (burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))

/-- The original reverse programme has a genuine full ambient strong limit. -/
theorem original_dual_tendsto (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => DualSource.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) atTop (𝓝 (value coordinate)) :=
  (original_dual_cauchy coordinate).tendsto_limUnder

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountingDual
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
