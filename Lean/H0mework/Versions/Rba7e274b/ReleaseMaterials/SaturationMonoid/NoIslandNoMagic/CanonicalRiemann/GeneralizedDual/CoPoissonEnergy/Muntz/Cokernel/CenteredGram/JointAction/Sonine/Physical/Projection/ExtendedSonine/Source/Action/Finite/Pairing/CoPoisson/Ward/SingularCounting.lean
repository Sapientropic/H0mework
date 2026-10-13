import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingPrimitive
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SingularCounting

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def powerRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((|x| : ℝ) : ℂ) ^ (star coordinate.value - 1)

theorem power_memLp (coordinate : BurnolCompletedMellinCoordinate) : MemLp (powerRaw coordinate) 2 μq := by
  have measured : Measurable (powerRaw coordinate) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const |x| (star coordinate.value - 1)
      (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt |>.continuousWithinAt
  apply (memLp_two_iff_integrable_sq_norm measured.aestronglyMeasurable).mpr
  have exponent : -1 < (2 * (coordinate.value.re - 1) : ℝ) := by linarith [coordinate.rightHalf]
  have native := (intervalIntegral.intervalIntegrable_cpow'
    (r := ((2 * (coordinate.value.re - 1) : ℝ) : ℂ)) (by simpa using exponent)
    (a := -q) (b := q)).norm
  have integral : Integrable (fun x : ℝ => ‖(x : ℂ) ^ ((2 * (coordinate.value.re - 1) : ℝ) : ℂ)‖) μq :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : -q ≤ q)).mp native
  apply integral.congr
  filter_upwards [ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))] with x nonzero
  simp only [powerRaw, Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr nonzero), sub_re, star_def, conj_re, one_re]
  rw [show (2 * (coordinate.value.re - 1)) = (coordinate.value.re - 1) * 2 by ring,
    Real.rpow_mul (abs_nonneg x), Real.rpow_two]

def powerL2 (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  (power_memLp coordinate).toLp (powerRaw coordinate)

theorem power_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (powerL2 coordinate : ℝ → ℂ) =ᵐ[μq] powerRaw coordinate := (power_memLp coordinate).coeFn_toLp

def centeredPower (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (powerL2 coordinate)

private theorem window_preserved (scale x : ℝ) (large : 1 ≤ scale) (inside : x ∈ symmetricInterval q) :
    x / scale ∈ symmetricInterval q := by
  apply abs_le.mp
  have xBound : |x| ≤ q := abs_le.mpr inside
  rw [abs_div, abs_of_pos (zero_lt_one.trans_le large), div_le_iff₀ (zero_lt_one.trans_le large)]
  exact xBound.trans (le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ q) large)

theorem counting_power (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    InverseAction.countingWindow scale (powerL2 coordinate) =
      (scale : ℂ) ^ (-star coordinate.value) • powerL2 coordinate := by
  have positive := zero_lt_one.trans_le large
  have scaleNe : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have powerNe : (scale : ℂ) ^ star coordinate.value ≠ 0 := by simp [scaleNe]
  apply Lp.ext
  filter_upwards [InverseAction.countingWindow_raw scale positive (powerL2 coordinate)
    (powerRaw coordinate) (power_coeFn coordinate),
    Lp.coeFn_smul ((scale : ℂ) ^ (-star coordinate.value)) (powerL2 coordinate),
    power_coeFn coordinate, ae_restrict_mem (measurableSet_symmetricInterval q)]
      with x countAt smulAt rawAt inside
  rw [countAt, smulAt]
  change InverseAction.countingRaw scale (powerRaw coordinate) x =
    (scale : ℂ) ^ (-star coordinate.value) * powerL2 coordinate x
  rw [rawAt]
  unfold InverseAction.countingRaw powerRaw
  rw [indicator_of_mem (window_preserved scale x large inside), abs_div, abs_of_pos positive,
    Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (abs_nonneg x) positive.le,
    Complex.cpow_sub _ _ scaleNe, cpow_one, cpow_neg]
  field_simp [scaleNe, powerNe]

theorem counting_constant (scale : ℝ) (large : 1 ≤ scale) :
    InverseAction.countingWindow scale (intervalConstant q) =
      (scale : ℂ)⁻¹ • intervalConstant q := by
  apply Lp.ext
  filter_upwards [InverseAction.countingWindow_raw scale (zero_lt_one.trans_le large)
    (intervalConstant q) (fun _ => (1 : ℂ)) (intervalConstant_coeFn q),
    Lp.coeFn_smul (scale : ℂ)⁻¹ (intervalConstant q), intervalConstant_coeFn q,
    ae_restrict_mem (measurableSet_symmetricInterval q)] with x countAt smulAt rawAt inside
  rw [countAt, smulAt]
  change InverseAction.countingRaw scale (fun _ => (1 : ℂ)) x = (scale : ℂ)⁻¹ * intervalConstant q x
  rw [rawAt]
  unfold InverseAction.countingRaw
  rw [indicator_of_mem (window_preserved scale x large inside)]

/-- The same original quarter mean removes the transported constant, leaving
the singular source's actual counting character for every scale at least one. -/
theorem centered_power_scale (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    InverseAction.centeredCounting scale (centeredPower coordinate) =
      (scale : ℂ) ^ (-star coordinate.value) • centeredPower coordinate := by
  have sourceRead : InverseAction.countingWindow scale (centeredPower coordinate : BurnolQuarterIntervalL2) =
      InverseAction.countingWindow scale (powerL2 coordinate) -
        burnolQuarterMeanCoefficient (powerL2 coordinate) • InverseAction.countingWindow scale (intervalConstant q) := by
    rw [centeredPower, Constructor.zeroMean_read]
    simp only [InverseAction.countingWindow, map_sub, map_smul, smul_sub, smul_smul]
    module
  unfold InverseAction.centeredCounting
  rw [sourceRead, counting_power coordinate scale large, counting_constant scale large,
    map_sub, map_smul, map_smul, map_smul, Constructor.zeroMean_constant, smul_zero, smul_zero, sub_zero]
  rfl

private def quarterCenter : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean.comp burnolQuarterRestriction

private theorem counting_eq_actual (scale : ℝ) (state : BurnolQuarterMeanZeroCarrier) :
    InverseAction.centeredCounting scale state =
      quarterCenter (ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension state)) := by
  simp only [InverseAction.centeredCounting, InverseAction.countingWindow, quarterCenter,
    ContinuousLinearMap.comp_apply, ContinuousChannels.channel, neg_one_mul, map_smul]

private theorem counting_integrable (upper : ℝ) (state : BurnolQuarterMeanZeroCarrier) :
    IntegrableOn (fun scale => InverseAction.centeredCounting scale state) (Ioc 0 upper) := by
  simpa only [IntegrableOn, ← counting_eq_actual] using
    quarterCenter.integrable_comp (ContinuousChannels.channel_integrable (-1) upper
      (burnolQuarterZeroExtension state))

/-- The normalized finite source is projected back through the original quarter window. -/
def projectedSource (N : ℕ) (state : BurnolQuarterMeanZeroCarrier) : BurnolQuarterMeanZeroCarrier :=
  quarterCenter (FiniteForcing.source N (burnolQuarterZeroExtension state))

private theorem projectedSource_eq (N : ℕ) (state : BurnolQuarterMeanZeroCarrier) :
    projectedSource N state =
      (∑ n ∈ Finset.Ico 1 N, InverseAction.centeredCounting n state) -
        ∫ scale : ℝ in Ioc 0 (N : ℝ), InverseAction.centeredCounting scale state := by
  unfold projectedSource FiniteForcing.source ContinuousChannels.normalization
  rw [map_sub, map_sum,
    ← quarterCenter.integral_comp_comm (ContinuousChannels.channel_integrable (-1) N
      (burnolQuarterZeroExtension state))]
  simp only [← counting_eq_actual, Channels.sourceChannel,
    show ∀ n : ℕ, (Real.sqrt (n : ℝ) : ℂ)⁻¹ •
      burnolMultiplicativeDilation (-Real.log (n : ℝ)) (burnolQuarterZeroExtension state) =
        ContinuousChannels.channel (-1) n (burnolQuarterZeroExtension state) from
      fun n => by simp only [ContinuousChannels.channel, neg_one_mul]]

/-- This retains the actual shrinking-window source for all scales from zero to one. -/
def smallScaleResidual (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  (1 / (1 - star coordinate.value)) • centeredPower coordinate -
    ∫ scale : ℝ in Ioc 0 1, InverseAction.centeredCounting scale (centeredPower coordinate)

/-- The same N coefficient is separated from the complete small-scale window residual. -/
theorem projected_power_source (coordinate : BurnolCompletedMellinCoordinate)
    (N : ℕ) (positive : 0 < N) :
    projectedSource N (centeredPower coordinate) =
      FiniteForcing.coefficient (star coordinate.value) N • centeredPower coordinate +
        smallScaleResidual coordinate := by
  have after : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have sourceIntegral := counting_integrable (N : ℝ) (centeredPower coordinate)
  have split : (∫ scale : ℝ in Ioc 0 (N : ℝ),
      InverseAction.centeredCounting scale (centeredPower coordinate)) =
        (∫ scale : ℝ in Ioc 0 1, InverseAction.centeredCounting scale (centeredPower coordinate)) +
          ∫ scale : ℝ in Ioc 1 (N : ℝ), InverseAction.centeredCounting scale (centeredPower coordinate) := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one after]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (sourceIntegral.mono_set (Ioc_subset_Ioc le_rfl after))
      (sourceIntegral.mono_set (Ioc_subset_Ioc zero_le_one le_rfl))
  have largeIntegral : (∫ scale : ℝ in Ioc 1 (N : ℝ),
      InverseAction.centeredCounting scale (centeredPower coordinate)) =
        (((N : ℂ) ^ (1 - star coordinate.value) - 1) / (1 - star coordinate.value)) •
          centeredPower coordinate := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun scale inside =>
      centered_power_scale coordinate scale inside.1.le), integral_smul_const,
      ← intervalIntegral.integral_of_le after]
    congr 1
    have exponent : -1 < (-star coordinate.value).re := by
      simpa only [neg_re, star_def, conj_re] using neg_lt_neg coordinate.belowOne
    rw [integral_cpow (Or.inl exponent), show -star coordinate.value + 1 = 1 - star coordinate.value by ring,
      Complex.ofReal_natCast, Complex.ofReal_one, one_cpow]
  rw [projectedSource_eq, split, largeIntegral]
  have integers : (∑ n ∈ Finset.Ico 1 N, InverseAction.centeredCounting n (centeredPower coordinate)) =
      (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-star coordinate.value)) • centeredPower coordinate := by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro n inside
    simpa only [Complex.ofReal_natCast] using centered_power_scale coordinate n
      (by exact_mod_cast (Finset.mem_Ico.mp inside).1)
  rw [integers]
  unfold FiniteForcing.coefficient smallScaleResidual
  rw [sub_div]
  module

/-- At the original zero, the singular component retains the actual 0..1
window residual; no individual counting operation is assigned a zero read. -/
theorem projected_power_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N => projectedSource N (centeredPower coordinate)) atTop
      (𝓝 (smallScaleResidual coordinate)) := by
  have arithmetic := ((DirichletCoefficient.original_coefficient_limits coordinate zero).1.smul_const
    (centeredPower coordinate)).add_const (smallScaleResidual coordinate)
  simp only [zero_smul, zero_add] at arithmetic
  apply arithmetic.congr'
  filter_upwards [eventually_ge_atTop 1] with N after
  exact (projected_power_source coordinate N (Nat.lt_of_lt_of_le (by decide : 0 < 1) after)).symm

def originalSingularSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterMeanZeroCarrier :=
  ForcingPrimitive.leadingCoefficient coordinate • centeredPower coordinate

private theorem projectedSource_smul (N : ℕ) (scalar : ℂ) (state : BurnolQuarterMeanZeroCarrier) :
    projectedSource N (scalar • state) = scalar • projectedSource N state := by
  unfold projectedSource
  rw [SetLike.val_smul, map_smul burnolQuarterZeroExtension,
    ← map_smul quarterCenter scalar (FiniteForcing.source N (burnolQuarterZeroExtension state))]
  congr 1
  unfold FiniteForcing.source ContinuousChannels.normalization
  rw [smul_sub, Finset.smul_sum, ← integral_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro n _
    simp only [Channels.sourceChannel, map_smul, smul_smul]
    rw [mul_comm]
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro scale _
    simp only [ContinuousChannels.channel, map_smul, smul_smul]
    rw [mul_comm]

/-- The original q-endpoint coefficient is transported with its own singular source and residual. -/
theorem original_singular_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N => projectedSource N (originalSingularSource coordinate)) atTop
      (𝓝 (ForcingPrimitive.leadingCoefficient coordinate • smallScaleResidual coordinate)) := by
  simpa only [originalSingularSource, projectedSource_smul] using!
    (projected_power_limit coordinate zero).const_smul (ForcingPrimitive.leadingCoefficient coordinate)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SingularCounting
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
