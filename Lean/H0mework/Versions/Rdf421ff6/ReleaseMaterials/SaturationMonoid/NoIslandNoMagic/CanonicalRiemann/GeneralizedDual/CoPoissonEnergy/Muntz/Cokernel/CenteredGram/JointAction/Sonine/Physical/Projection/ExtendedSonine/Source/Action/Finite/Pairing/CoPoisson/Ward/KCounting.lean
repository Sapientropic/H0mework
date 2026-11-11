import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingLimit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.KCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource OriginalRieszSourceGreen
noncomputable section

/-- Fourier exchanges the two complete finite channels, including the entire small-scale integral. -/
theorem dual_fourier (N : ℕ) (seed : BurnolL2) :
    DualSource.source N (fourierL2 seed) = fourierL2 (FiniteForcing.source N seed) := by
  have channel (a : ℝ) : ContinuousChannels.channel 1 a (fourierL2 seed) =
      fourierL2 (ContinuousChannels.channel (-1) a seed) := by
    simp only [ContinuousChannels.channel, one_mul, neg_one_mul, map_smul, fourierL2_burnolMultiplicativeDilation, neg_neg]
  have integer (n : ℕ) : ContinuousChannels.channel 1 n (fourierL2 seed) =
      fourierL2 (Channels.sourceChannel n seed) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, neg_one_mul] using channel n
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) N seed)

theorem original_kernel_raw (coordinate : BurnolCompletedMellinCoordinate) :
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) -
        PositionCounting.seedRaw coordinate x -
          fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) x := by
  have whole := KCountingSource.base_coeFn coordinate
  rw [KCountingSource.base_eq_kernel] at whole
  filter_upwards [whole, Lp.coeFn_add (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    (fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))]
    with x read addition
  rw [addition, Pi.add_apply, KCountingSource.baseRaw_synthesis] at read
  exact eq_sub_of_add_eq read

/-- The original K, the actual L¹ position source and the original Fourier source share this full distributional reading. -/
theorem original_kernel_read (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : TemperedDistribution ℝ ℂ) test =
      (∫ x : ℝ, ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)) * test x) -
        PositionEuler.source coordinate test -
          (fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) :
            TemperedDistribution ℝ ℂ) test := by
  have baseProduct : Integrable (fun x : ℝ => KCountingSource.baseRaw coordinate x * test x) := by
    have actual : Integrable (fun x : ℝ => KCountingSource.base coordinate x * test x) :=
      memLp_one_iff_integrable.mp ((test.memLp 2 volume).mul' (Lp.memLp (KCountingSource.base coordinate)))
    apply actual.congr
    filter_upwards [KCountingSource.base_coeFn coordinate] with x read
    rw [read]
  have positionProduct := (PositionEuler.seed_integrable coordinate).mul_bdd test.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => SchwartzMap.norm_le_seminorm ℝ test x))
  have complete : (KCountingSource.base coordinate : TemperedDistribution ℝ ℂ) test + PositionEuler.source coordinate test =
      ∫ x : ℝ, ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)) * test x := by
    rw [Lp.toTemperedDistribution_apply, PositionChannel.source_raw_read]
    have baseRead : (∫ x : ℝ, test x • KCountingSource.base coordinate x) =
        ∫ x : ℝ, KCountingSource.baseRaw coordinate x * test x := by
      apply integral_congr_ae
      filter_upwards [KCountingSource.base_coeFn coordinate] with x read
      rw [read, smul_eq_mul, mul_comm]
    rw [baseRead, ← integral_add baseProduct positionProduct]
    apply integral_congr_ae
    filter_upwards with x
    rw [KCountingSource.baseRaw_synthesis]
    ring
  rw [KCountingSource.base_eq_kernel] at complete
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)))) test + _ = _ at complete
  rw [map_add, add_apply] at complete
  simp only [Lp.toTemperedDistributionCLM_apply] at complete
  linear_combination complete

theorem original_finite (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    DualSource.source N (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      KCountingSource.finite coordinate N - fourierL2 (FiniteForcing.source N
        (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) := by
  have source : (burnolCompletedMellinRieszVector coordinate : BurnolL2) = KCountingSource.base coordinate -
      fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
    rw [KCountingSource.base_eq_kernel, add_sub_cancel_right]
  rw [source, CountingDual.dual_eq_adjoint, map_sub, ← CountingDual.dual_eq_adjoint,
    ← CountingDual.dual_eq_adjoint, dual_fourier]
  rfl

/-- The original Riesz K itself now has its source-generated complete reverse-counting strong limit. -/
theorem original_tendsto (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => DualSource.source N (burnolCompletedMellinRieszVector coordinate : BurnolL2)) atTop
      (𝓝 (-PositionCounting.value coordinate zero - burnolTateReciprocalL2 (CountingDual.value coordinate))) := by
  have fourier := (fourierL2.continuous.tendsto (AmbientCounting.value coordinate)).comp (AmbientCounting.original_ambient_limit coordinate)
  have actual := (KCountingSource.finite_tendsto coordinate zero).sub fourier
  have identity : fourierL2 (AmbientCounting.value coordinate) = burnolTateReciprocalL2 (CountingDual.value coordinate) := by
    rw [DualLanding.original_tate_fourier, burnolTateReciprocalL2_involutive]
  rw [identity] at actual
  exact actual.congr' (Eventually.of_forall (fun N => (original_finite coordinate N).symm))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.KCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
