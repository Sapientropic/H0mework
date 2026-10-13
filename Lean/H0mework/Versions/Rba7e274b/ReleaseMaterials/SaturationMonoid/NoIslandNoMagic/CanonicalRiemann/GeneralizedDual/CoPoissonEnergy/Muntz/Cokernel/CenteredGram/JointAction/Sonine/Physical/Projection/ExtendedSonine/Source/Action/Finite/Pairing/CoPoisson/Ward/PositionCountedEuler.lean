import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionChannel
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.EdgeSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionCountedEuler

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

theorem raw_outside (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (x : ℝ) (outside : q < |x|) :
    PositionCounting.raw coordinate N x = 0 := by
  by_cases atZero : N = 0
  · subst N
    simp [PositionCounting.raw]
  have positive : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr atZero
  have absolute : 0 < |x| := (by norm_num : (0 : ℝ) < q).trans outside
  have covered : q ≤ (N : ℝ) * |x| := outside.le.trans (by nlinarith)
  rw [PositionCounting.raw, PositionCounting.continuous_raw_zero coordinate N x (abs_pos.mp absolute) covered,
    sub_zero]
  apply Finset.sum_eq_zero
  intro n member
  have lower : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp member).1
  have large : q < |(n : ℝ) * x| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    nlinarith
  rw [PositionCounting.seedRaw, if_neg large.not_ge]

theorem finite_integrable (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) : Integrable (PositionCounting.raw coordinate N) := by
  have compact := (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr
    (PositionCountingLimit.finite_integrable coordinate zero N)
  apply compact.congr
  filter_upwards with x
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside, raw_outside coordinate N x
      (lt_of_not_ge (fun h => inside (abs_le.mp h)))]

private theorem value_integrable (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Integrable (PositionCounting.value coordinate zero : ℝ → ℂ) := by
  have localValue : Integrable (PositionCounting.value coordinate zero : ℝ → ℂ) μq :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      ((Lp.memLp (PositionCounting.value coordinate zero)).mono_measure Measure.restrict_le_self)
  have compact := (integrable_indicator_iff (measurableSet_symmetricInterval q)).mpr localValue
  apply compact.congr
  filter_upwards [PositionCounting.value_coeFn coordinate zero] with x source
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside, source, PositionCounting.event_outside coordinate x
      (lt_of_not_ge (fun h => inside (abs_le.mp h)))]

private def finiteL1 (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) : Lp ℂ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.mpr (finite_integrable coordinate zero N)).toLp (PositionCounting.raw coordinate N)

/-- The actual finite position programme has its genuine L¹ tempered realization. -/
def source (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) : TemperedDistribution ℝ ℂ :=
  Lp.toTemperedDistributionCLM ℂ volume 1 (finiteL1 coordinate zero N)

theorem source_read (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    source coordinate zero N test = ∫ x : ℝ, PositionCounting.raw coordinate N x * test x := by
  rw [source, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.mpr (finite_integrable coordinate zero N)).coeFn_toLp] with x same
  change test x • finiteL1 coordinate zero N x = _
  rw [finiteL1, same]
  simp only [smul_eq_mul, mul_comm]

theorem finite_euler (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) (test : SchwartzMap ℝ ℂ) :
    GapEuler.euler (source coordinate zero N) test =
      -(star coordinate.value - 1 / 2) * source coordinate zero N test +
      Kernel.A coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test +
      Kernel.A coordinate * DualEuler.edgeProgramme N test := by
  rw [PositionChannel.euler_read, source_read, source_read]
  exact PositionChannel.finite_euler coordinate N test

private theorem whole_error (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (N : ℕ) :
    (∫ x : ℝ, ‖PositionCounting.raw coordinate N x - PositionCounting.value coordinate zero x‖) =
      ∫ x : ℝ in symmetricInterval q, ‖PositionCounting.raw coordinate N x - PositionCounting.value coordinate zero x‖ := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [PositionCounting.value_coeFn coordinate zero] with x source outside
  have large := lt_of_not_ge (fun h => outside (abs_le.mp h))
  rw [raw_outside coordinate N x large, source, PositionCounting.event_outside coordinate x large, sub_self, norm_zero]

/-- The entire original q L¹ limit controls every Schwartz test, including the Euler test. -/
theorem original_weak_limit (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ => source coordinate zero N test) atTop
      (𝓝 ((PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test)) := by
  let rawMem (N : ℕ) := memLp_one_iff_integrable.mpr (finite_integrable coordinate zero N)
  let valueMem := memLp_one_iff_integrable.mpr (value_integrable coordinate zero)
  let limitL1 : Lp ℂ 1 (volume : Measure ℝ) := valueMem.toLp (PositionCounting.value coordinate zero : ℝ → ℂ)
  have strong : Tendsto (finiteL1 coordinate zero) atTop (𝓝 limitL1) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (PositionCounting.raw coordinate ·) rawMem
      (PositionCounting.value coordinate zero : ℝ → ℂ) valueMem).mpr
    have integralLimit := (PositionCountingLimit.finite_tendsto_value_L1 coordinate zero).congr'
      (Eventually.of_forall (fun N => (whole_error coordinate zero N).symm))
    have extended := ENNReal.continuous_ofReal.tendsto 0 |>.comp integralLimit
    convert extended using 1
    · ext N
      rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) ((rawMem N).sub valueMem)]
      simp
    · simp
  let reader : Lp ℂ 1 (volume : Measure ℝ) →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp (Lp.toTemperedDistributionCLM ℂ volume 1)
  have actual := (reader.continuous.tendsto limitL1).comp strong
  have identifies : reader limitL1 = (PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test := by
    change (Lp.toTemperedDistributionCLM ℂ volume 1 limitL1) test = _
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [valueMem.coeFn_toLp] with x same
    change test x • limitL1 x = _
    rw [same]
  rw [identifies] at actual
  exact actual

/-- The complementary original response has the full computed sawtooth contact. -/
theorem original_response_limit (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0)
    (test : SchwartzMap ℝ ℂ) :
    Tendsto (fun N : ℕ =>
      Kernel.A coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test) atTop
      (𝓝 (GapEuler.euler (PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test +
        (star coordinate.value - 1 / 2) * (PositionCounting.value coordinate zero : TemperedDistribution ℝ ℂ) test +
        Kernel.A coordinate * (GapEuler.euler (ConstantDual.value : TemperedDistribution ℝ ℂ) test +
          (1 / 2 : ℂ) * (ConstantDual.value : TemperedDistribution ℝ ℂ) test))) := by
  have first := original_weak_limit coordinate zero (PositionChannel.eulerCotest test)
  simp only [← PositionChannel.euler_read] at first
  have actual := (first.add ((original_weak_limit coordinate zero test).const_mul
    (star coordinate.value - 1 / 2))).sub ((EdgeSource.programme_limit test).const_mul (Kernel.A coordinate))
  have same (N : ℕ) := finite_euler coordinate zero N test
  have inputs : (fun N : ℕ => GapEuler.euler (source coordinate zero N) test +
      (star coordinate.value - 1 / 2) * source coordinate zero N test -
      Kernel.A coordinate * DualEuler.edgeProgramme N test) =
      (fun N : ℕ => Kernel.A coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.v : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test -
      Kernel.beta coordinate * (DualSource.source N (burnolQuarterZeroExtension
        (Response.u : BurnolQuarterIntervalL2)) : TemperedDistribution ℝ ℂ) test) := by
    funext N
    rw [same N]
    ring
  rw [inputs] at actual
  convert actual using 1
  congr 1
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionCountedEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
