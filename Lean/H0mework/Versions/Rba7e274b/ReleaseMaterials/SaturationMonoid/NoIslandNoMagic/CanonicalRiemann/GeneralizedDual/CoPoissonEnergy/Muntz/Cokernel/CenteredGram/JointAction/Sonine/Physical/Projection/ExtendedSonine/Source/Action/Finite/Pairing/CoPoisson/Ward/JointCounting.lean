import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionEuler
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCountingLimit
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualLanding

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.JointCounting

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def profile (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  Kernel.beta coordinate * positionSource coordinate x +
    Kernel.A coordinate * burnolRieszSingleFourierSourceRaw coordinate x

def seedRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x| ≤ q then profile coordinate |x| else 0

def raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), seedRaw coordinate (a * x)

def eventRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ∑ n ∈ DualSourceRaw.channels x, profile coordinate ((n : ℝ) * |x|)

/-- Both endpoint readings belong to the same original Riesz source. -/
theorem profile_endpoint (coordinate : BurnolCompletedMellinCoordinate) : profile coordinate q = 0 := by
  rw [profile, Energy.Margin.positionSource_endpoint, Energy.Margin.fourierSource_endpoint]
  ring

theorem profile_continuousAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (positive : 0 < x) : ContinuousAt (profile coordinate) x :=
  (continuousAt_const.mul (positionSource_continuousAt coordinate positive)).add
    (continuousAt_const.mul (burnolRieszSingleFourierSourceRaw_continuousAt coordinate positive.ne'))

theorem seed_split (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    seedRaw coordinate x = Kernel.beta coordinate * PositionCounting.seedRaw coordinate x +
      Kernel.A coordinate * DualSourceRaw.seedRaw coordinate x := by
  have absolute : burnolRieszSingleFourierSourceRaw coordinate |x| =
      burnolRieszSingleFourierSourceRaw coordinate x := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, source_raw_even]
  by_cases inside : |x| ≤ q
  · rw [seedRaw, PositionCounting.seedRaw, if_pos inside, if_pos inside, DualSourceRaw.seedRaw,
      indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside), profile, absolute]
  · rw [seedRaw, PositionCounting.seedRaw, if_neg inside, if_neg inside, DualSourceRaw.seedRaw,
      indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h))]
    simp

/-- The actual cancellation at q gives continuity also across both cutoff edges. -/
theorem seed_continuousAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (nonzero : x ≠ 0) : ContinuousAt (seedRaw coordinate) x := by
  have actual : ContinuousAt (fun y : ℝ => profile coordinate |y|) x :=
    (profile_continuousAt coordinate |x| (abs_pos.mpr nonzero)).comp continuous_abs.continuousAt
  by_cases boundary : |x| = q
  · change Tendsto _ _ (𝓝 (seedRaw coordinate x))
    have center : seedRaw coordinate x = 0 := by
      rw [seedRaw, if_pos boundary.le, boundary, profile_endpoint]
    rw [center]
    apply Filter.Tendsto.if'
    · simpa only [boundary, profile_endpoint] using actual.tendsto
    · exact tendsto_const_nhds
  · by_cases inside : |x| < q
    · apply actual.congr_of_eventuallyEq
      filter_upwards [continuous_abs.continuousAt.eventually_lt_const inside] with y small
      exact if_pos small.le
    · have outside : q < |x| := lt_of_le_of_ne (le_of_not_gt inside) (Ne.symm boundary)
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [continuous_abs.continuousAt.eventually_const_lt outside] with y large
      exact if_neg (not_le.mpr large)

private theorem fourier_seed_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (DualSourceRaw.seedRaw coordinate) := by
  apply (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr
  exact ((Lp.memLp (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)).integrable
    (by norm_num)).congr (burnolRieszSingleFourierSource_ae_raw coordinate)

theorem seed_integrable (coordinate : BurnolCompletedMellinCoordinate) : Integrable (seedRaw coordinate) := by
  apply (((PositionEuler.seed_integrable coordinate).const_mul (Kernel.beta coordinate)).add
    ((fourier_seed_integrable coordinate).const_mul (Kernel.A coordinate))).congr
  filter_upwards with x
  exact (seed_split coordinate x).symm

private theorem slice_integrable (f : ℝ → ℂ) (integrable : Integrable f) (N : ℕ) (x : ℝ) :
    IntegrableOn (fun a : ℝ => f (a * x)) (Ioc 0 (N : ℝ)) := by
  by_cases nonzero : x = 0
  · subst x
    simpa only [mul_zero] using
      (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self :
        IntegrableOn (fun _ : ℝ => f 0) (Ioc 0 (N : ℝ)))
  · exact (integrable.comp_mul_right' nonzero).integrableOn

/-- This is the same finite cutoff and the entire continuous channel on 0 < a ≤ N. -/
theorem raw_split (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) :
    raw coordinate N x = Kernel.beta coordinate * PositionCounting.raw coordinate N x +
      Kernel.A coordinate * DualSourceRaw.raw coordinate N x := by
  have first := (slice_integrable _ (PositionEuler.seed_integrable coordinate) N x).const_mul (Kernel.beta coordinate)
  have second := (slice_integrable _ (fourier_seed_integrable coordinate) N x).const_mul (Kernel.A coordinate)
  unfold raw PositionCounting.raw DualSourceRaw.raw
  simp_rw [seed_split]
  rw [integral_add first second, integral_const_mul, integral_const_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem event_split (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    eventRaw coordinate x = Kernel.beta coordinate * PositionCounting.eventRaw coordinate x +
      Kernel.A coordinate * DualSourceRaw.eventRaw coordinate x := by
  simp only [eventRaw, profile, PositionCounting.eventRaw, DualSourceRaw.eventRaw,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem raw_event (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) : raw coordinate N x = eventRaw coordinate x := by
  rw [raw_split, PositionCounting.raw_event coordinate N x nonzero complete,
    DualSourceRaw.raw_event coordinate N x nonzero complete, event_split]

theorem raw_eventually (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (nonzero : x ≠ 0) :
    ∀ᶠ N : ℕ in atTop, raw coordinate N x = eventRaw coordinate x := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (q / |x|))]
    with N complete
  exact raw_event coordinate N x nonzero complete

theorem event_eq_sum (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ)
    (nonzero : x ≠ 0) (complete : q / |x| < (N : ℝ)) :
    eventRaw coordinate x = ∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * x) := by
  have covered : q ≤ (N : ℝ) * |x| := ((div_lt_iff₀ (abs_pos.mpr nonzero)).mp complete).le
  rw [event_split, ← PositionCounting.raw_event coordinate N x nonzero complete,
    ← DualSourceRaw.raw_event coordinate N x nonzero complete, PositionCounting.raw, DualSourceRaw.raw,
    PositionCounting.continuous_raw_zero coordinate N x nonzero covered,
    DualSourceRaw.continuous_raw_zero coordinate N x nonzero covered]
  simp_rw [seed_split]
  simp only [sub_zero, Finset.sum_add_distrib, Finset.mul_sum]

/-- A locally finite sum of the actual continuous channels includes every q/n boundary. -/
theorem event_continuousAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (nonzero : x ≠ 0) : ContinuousAt (eventRaw coordinate) x := by
  obtain ⟨N, complete⟩ := exists_nat_gt (q / |x|)
  have finite : ContinuousAt (fun y : ℝ => ∑ n ∈ Finset.Ico 1 N, seedRaw coordinate ((n : ℝ) * y)) x := by
    apply tendsto_finsetSum
    intro n inside
    have positive : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp inside).1
    exact (seed_continuousAt coordinate ((n : ℝ) * x) (mul_ne_zero positive.ne' nonzero)).comp
      (continuousAt_const.mul continuousAt_id)
  apply finite.congr_of_eventuallyEq
  have quotient : ContinuousAt (fun y : ℝ => q / |y|) x :=
    continuousAt_const.div continuous_abs.continuousAt (abs_pos.mpr nonzero).ne'
  filter_upwards [quotient.eventually_lt_const complete,
    continuous_abs.continuousAt.eventually_const_lt (abs_pos.mpr nonzero)] with y bound positive
  exact event_eq_sum coordinate N y (abs_pos.mp positive) bound

theorem event_collar (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (lower : q / 2 < |x|) (upper : |x| ≤ q) : eventRaw coordinate x = profile coordinate |x| := by
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q / 2).trans lower
  have index : ⌊q / |x|⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ q / |x|)]
    constructor
    · norm_num
      exact (le_div_iff₀ absolute).mpr (by simpa using upper)
    · norm_num
      exact (div_lt_iff₀ absolute).mpr (by linarith)
  rw [eventRaw, DualSourceRaw.channels, index, Finset.Icc_self, Finset.sum_singleton]
  simp

theorem event_endpoint (coordinate : BurnolCompletedMellinCoordinate) : eventRaw coordinate q = 0 := by
  rw [event_collar coordinate q (by norm_num) (by norm_num),
    abs_of_pos (by norm_num : (0 : ℝ) < q), profile_endpoint]

def value (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) : BurnolL2 :=
  Kernel.beta coordinate • PositionCounting.value coordinate zero +
    Kernel.A coordinate • CountingDual.value coordinate

theorem value_coeFn (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    (value coordinate zero : ℝ → ℂ) =ᵐ[volume] eventRaw coordinate := by
  filter_upwards [Lp.coeFn_add (Kernel.beta coordinate • PositionCounting.value coordinate zero)
      (Kernel.A coordinate • CountingDual.value coordinate),
    Lp.coeFn_smul (Kernel.beta coordinate) (PositionCounting.value coordinate zero),
    Lp.coeFn_smul (Kernel.A coordinate) (CountingDual.value coordinate),
    PositionCounting.value_coeFn coordinate zero, DualLanding.original_coeFn coordinate]
    with x addition first second position fourier
  change ((Kernel.beta coordinate • PositionCounting.value coordinate zero +
      Kernel.A coordinate • CountingDual.value coordinate : BurnolL2) x) = _
  rw [addition, Pi.add_apply, first, second, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, position, fourier, event_split]

def source (coordinate : BurnolCompletedMellinCoordinate) : TemperedDistribution ℝ ℂ :=
  Kernel.beta coordinate • PositionEuler.source coordinate +
    Kernel.A coordinate • (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ)

theorem source_read (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    source coordinate test = ∫ x : ℝ, seedRaw coordinate x * test x := by
  have first : PositionEuler.source coordinate test =
      ∫ x : ℝ, PositionCounting.seedRaw coordinate x * test x := by
    unfold PositionEuler.source
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [(memLp_one_iff_integrable.mpr (PositionEuler.seed_integrable coordinate)).coeFn_toLp]
      with x read
    rw [read]
    simp only [smul_eq_mul, mul_comm]
  have second : (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) test =
      ∫ x : ℝ, DualSourceRaw.seedRaw coordinate x * test x := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [DualSourceRaw.seedRaw_read coordinate] with x read
    rw [read]
    simp only [smul_eq_mul, mul_comm]
  have firstInt := (PositionEuler.seed_integrable coordinate).mul_bdd test.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => SchwartzMap.norm_le_seminorm ℝ test x))
  have secondInt := (fourier_seed_integrable coordinate).mul_bdd test.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => SchwartzMap.norm_le_seminorm ℝ test x))
  simp only [source, add_apply, smul_apply, smul_eq_mul]
  rw [first, second, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (firstInt.const_mul (Kernel.beta coordinate)) (secondInt.const_mul (Kernel.A coordinate))]
  apply integral_congr_ae
  filter_upwards with x
  rw [seed_split]
  ring

private theorem fourier_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) =
      (star coordinate.value - 1 / 2) • (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) +
      Kernel.A coordinate • (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
      Kernel.beta coordinate • (burnolQuarterZeroExtension (Response.v : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
      Kernel.beta coordinate • GapEuler.edge q := by
  rw [Euler.source_euler, Euler.sourceEuler_eq]
  change Lp.toTemperedDistributionCLM ℂ volume 2 (burnolQuarterZeroExtension _) - _ = _
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, map_add, map_sub, map_smul]
  rfl

/-- The common source removes the actual edge and v contact; its u response remains explicit. -/
theorem original_euler (coordinate : BurnolCompletedMellinCoordinate) :
    GapEuler.euler (source coordinate) = (star coordinate.value - 1 / 2) •
      (Kernel.A coordinate • (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) -
          Kernel.beta coordinate • PositionEuler.source coordinate) +
      (Kernel.A coordinate ^ 2 - Kernel.beta coordinate ^ 2) •
        (burnolQuarterZeroExtension (Response.u : BurnolQuarterIntervalL2) : TemperedDistribution ℝ ℂ) := by
  rw [source, map_add, map_smul, map_smul, PositionEuler.original_euler, fourier_euler]
  module

end
end OriginalRieszFinitePairing.CoPoisson.Ward.JointCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
