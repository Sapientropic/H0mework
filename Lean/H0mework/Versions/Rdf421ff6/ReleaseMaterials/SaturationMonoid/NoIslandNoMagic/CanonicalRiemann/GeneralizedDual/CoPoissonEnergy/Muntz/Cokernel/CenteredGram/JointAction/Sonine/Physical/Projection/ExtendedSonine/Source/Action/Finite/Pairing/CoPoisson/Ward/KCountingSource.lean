import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCountedEuler
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualLanding
import H0mework.Versions.V2.Arithmetic.RieszGreen.KernelGram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.KCountingSource

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSourceGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

/-- The original reconstruction supplies this entire L² source before counting. -/
def base (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  gapState coordinate + burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2)

def baseRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  if |x| ≤ q then GapEuler.gapMean q coordinate + burnolRieszReturnRaw coordinate |x|
  else (1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)

theorem base_eq_kernel (coordinate : BurnolCompletedMellinCoordinate) : base coordinate =
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) +
      fourierL2 (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) := by
  rw [Kernel.original_kernel_reconstruction]
  rw [sub_add_cancel]
  rfl

theorem base_coeFn (coordinate : BurnolCompletedMellinCoordinate) : (base coordinate : ℝ → ℂ) =ᵐ[volume] baseRaw coordinate := by
  have returnRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (Constructor.returnState_read coordinate)
  filter_upwards [Lp.coeFn_add (gapState coordinate)
      (burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2)),
    gapState_read coordinate, burnolQuarterZeroExtension_coe (Constructor.returnState coordinate : BurnolQuarterIntervalL2),
    returnRead] with x addition gap extension returned
  change (gapState coordinate + burnolQuarterZeroExtension (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : BurnolL2) x = _
  rw [addition, Pi.add_apply, gap, extension]
  have absolute : burnolRieszReturnRaw coordinate |x| = burnolRieszReturnRaw coordinate x := by
    rcases le_total 0 x with positive | negative
    · rw [abs_of_nonneg positive]
    · rw [abs_of_nonpos negative, return_raw_even]
  by_cases inside : |x| ≤ q
  · rw [baseRaw, if_pos inside, gapState_raw_gap coordinate (abs_le.mp inside),
      indicator_of_mem (show x ∈ symmetricInterval q from abs_le.mp inside), returned (abs_le.mp inside), absolute]
  · have outside := lt_of_not_ge inside
    have even : burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x =
        burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) |x| := by
      rcases le_total 0 x with positive | negative
      · rw [abs_of_nonneg positive]
      · rw [abs_of_nonpos negative]
        unfold burnolEvenRaw
        simp only [neg_neg]
        ring
    rw [baseRaw, if_neg inside, indicator_of_notMem (show x ∉ symmetricInterval q from fun h => inside (abs_le.mpr h)),
      add_zero, even, gapState_raw_tail coordinate outside]

/-- The homogeneous term is an identity of raw functions; it is never assigned an L² summand. -/
theorem baseRaw_synthesis (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    baseRaw coordinate x = (1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) - PositionCounting.seedRaw coordinate x := by
  by_cases inside : |x| ≤ q
  · rw [baseRaw, PositionCounting.seedRaw, if_pos inside, if_pos inside, positionSource]
    ring
  · rw [baseRaw, PositionCounting.seedRaw, if_neg inside, if_neg inside, sub_zero]

theorem base_measurable (coordinate : BurnolCompletedMellinCoordinate) : Measurable (baseRaw coordinate) := by
  have power : Measurable (fun x : ℝ => ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    have nonzero : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using outside
    exact ((Complex.continuousAt_ofReal_cpow_const |x| (-star coordinate.value)
      (Or.inr (abs_pos.mpr nonzero).ne')).comp continuous_abs.continuousAt).continuousWithinAt
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_const.add ((burnolRieszReturnRaw_continuous coordinate).comp continuous_abs).measurable)
    (measurable_const.mul power)

def finite (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) : BurnolL2 := DualSource.source N (base coordinate)

def raw (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, baseRaw coordinate ((n : ℝ) * x)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), baseRaw coordinate (a * x)

private theorem normalization_coeFn (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    ((∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (base coordinate) : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ a : ℝ in Ioc 0 (N : ℝ), baseRaw coordinate (a * x) := by
  apply OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioc 0 (N : ℝ))) _
    (ContinuousChannels.channel_integrable 1 (N : ℝ) _) (fun p : ℝ × ℝ => baseRaw coordinate (p.1 * p.2))
    ((base_measurable coordinate).comp (by fun_prop))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a inside
  exact DualSourceRaw.channel_coeFn _ _ (base_coeFn coordinate) a inside.1

theorem finite_coeFn (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    (finite coordinate N : ℝ → ℂ) =ᵐ[volume] raw coordinate N := by
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      ContinuousChannels.channel 1 (n : ℝ) (base coordinate) x = baseRaw coordinate ((n : ℝ) * x) := by
    apply ae_all_iff.mpr
    intro n
    exact DualSourceRaw.channel_coeFn _ _ (base_coeFn coordinate) n
      (by exact_mod_cast (Finset.mem_Ico.mp n.2).1)
  filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) (base coordinate))
      (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (base coordinate)),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => ContinuousChannels.channel 1 (n : ℝ) (base coordinate)),
    normalization_coeFn coordinate N, channels] with x difference sum integral channel
  change ((∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel 1 (n : ℝ) (base coordinate)) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a (base coordinate) : BurnolL2) x = _
  rw [difference, Pi.sub_apply, sum, integral]
  unfold raw
  congr 1
  apply Finset.sum_congr rfl
  intro n inside
  exact channel ⟨n, inside⟩

theorem raw_synthesis (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ)
    (x : ℝ) (nonzero : x ≠ 0) :
    raw coordinate N x = (1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value) *
      FiniteForcing.coefficient (star coordinate.value) N - PositionCounting.raw coordinate N x := by
  have absolute : 0 < |x| := abs_pos.mpr nonzero
  have channel (a : ℝ) (positive : 0 < a) : baseRaw coordinate (a * x) =
      ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)) * (a : ℂ) ^ (-star coordinate.value) -
        PositionCounting.seedRaw coordinate (a * x) := by
    rw [baseRaw_synthesis, abs_mul, abs_of_pos positive, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg positive.le absolute.le]
    ring
  have power : IntervalIntegrable (fun a : ℝ => (a : ℂ) ^ (-star coordinate.value)) volume 0 N :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [neg_re, star_def, conj_re]; linarith [coordinate.belowOne])
  have seed : IntegrableOn (fun a : ℝ => PositionCounting.seedRaw coordinate (a * x)) (Ioc 0 (N : ℝ)) :=
    ((PositionEuler.seed_integrable coordinate).comp_mul_right' nonzero).integrableOn
  have integral : (∫ a : ℝ in Ioc 0 (N : ℝ), (a : ℂ) ^ (-star coordinate.value)) =
      (N : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value) := by
    have exponent : 1 - star coordinate.value ≠ 0 := by
      intro same
      have realPart := congrArg Complex.re same
      simp only [sub_re, one_re, star_def, conj_re, zero_re] at realPart
      linarith [coordinate.belowOne]
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      integral_cpow (Or.inl (by simp only [neg_re, star_def, conj_re]; linarith [coordinate.belowOne])),
      show -star coordinate.value + 1 = 1 - star coordinate.value by ring,
      ofReal_zero, zero_cpow exponent, sub_zero, Complex.ofReal_natCast]
  have discrete : (∑ n ∈ Finset.Ico 1 N, baseRaw coordinate ((n : ℝ) * x)) =
      ((1 / 2 : ℂ) * ((|x| : ℝ) : ℂ) ^ (-star coordinate.value)) *
        (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-star coordinate.value)) -
          ∑ n ∈ Finset.Ico 1 N, PositionCounting.seedRaw coordinate ((n : ℝ) * x) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n inside
    simpa only [Complex.ofReal_natCast] using channel n (by exact_mod_cast (Finset.mem_Ico.mp inside).1)
  unfold raw
  rw [discrete, setIntegral_congr_fun measurableSet_Ioc (fun a inside => channel a inside.1),
    integral_sub (power.1.const_mul _) seed, integral_const_mul, integral]
  unfold FiniteForcing.coefficient PositionCounting.raw
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.KCountingSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
