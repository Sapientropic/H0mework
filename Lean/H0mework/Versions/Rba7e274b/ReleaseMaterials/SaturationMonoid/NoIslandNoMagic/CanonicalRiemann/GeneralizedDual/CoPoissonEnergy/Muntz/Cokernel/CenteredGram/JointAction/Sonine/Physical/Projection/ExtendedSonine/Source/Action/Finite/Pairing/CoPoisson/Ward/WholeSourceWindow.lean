import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceCounting
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WindowCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.WholeSourceWindow

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward.InverseAction OriginalRieszFinitePairing.CoPoisson.Ward.InverseTail

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

def smoothState (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  burnolTruncatedFourier (Constructor.returnState coordinate : BurnolQuarterIntervalL2)

theorem smoothState_ae_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (smoothState coordinate : ℝ → ℂ) =ᵐ[μq] smoothFourier coordinate := by
  have raw := Constructor.fourierRaw_congr _ _ (Constructor.returnState_read coordinate)
  exact (Constructor.truncatedFourier_read _).trans (EventuallyEq.of_eq raw)

theorem smoothState_mean (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterMeanCoefficient (smoothState coordinate) = rawMean (smoothFourier coordinate) := by
  rw [Constructor.mean_integral, integral_congr_ae (smoothState_ae_raw coordinate)]
  rfl

/-- The full original q-window source, with its actual constant term retained. -/
theorem original_window_decomposition (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) =
      ForcingPrimitive.leadingCoefficient coordinate • SingularCounting.powerL2 coordinate +
        ForcingTail.forcingRemainderState coordinate + smoothState coordinate -
      (ForcingMeanZero.mean coordinate + burnolQuarterMeanCoefficient (smoothState coordinate)) • intervalConstant q := by
  have source := congrArg (fun state : BurnolQuarterMeanZeroCarrier => (state : BurnolQuarterIntervalL2))
    (WholeSourceCounting.original_b_decomposition coordinate)
  simp only [Submodule.coe_add, Submodule.coe_smul] at source
  rw [show (SingularCounting.centeredPower coordinate : BurnolQuarterIntervalL2) =
      SingularCounting.powerL2 coordinate - burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate) •
        intervalConstant q from Constructor.zeroMean_read _,
    show (ForcingTail.meanZeroRemainder coordinate : BurnolQuarterIntervalL2) =
      ForcingTail.forcingRemainderState coordinate -
        burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • intervalConstant q
      from Constructor.zeroMean_read _,
    show (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
        (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2) =
      smoothState coordinate - burnolQuarterMeanCoefficient (smoothState coordinate) • intervalConstant q
      from Constructor.zeroMean_read _] at source
  rw [source, WholeSourceCounting.original_mean_balance]
  module

private theorem window_norm_bound (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) (bound scale : ℝ)
    (nonnegative : 0 ≤ bound) (large : 1 ≤ scale)
    (pointwise : ∀ x ∈ symmetricInterval q, ‖raw (x / scale)‖ ≤ bound * scale⁻¹ ^ 2) :
    ‖countingWindow scale state‖ ≤ bound * scale⁻¹ ^ 3 := by
  have positive : 0 < scale := zero_lt_one.trans_le large
  have compared : ‖countingWindow scale state‖ ≤ (bound * scale⁻¹ ^ 3) * ‖intervalConstant q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [countingWindow_raw scale positive state raw represents,
      ae_restrict_mem (measurableSet_symmetricInterval q), intervalConstant_coeFn q] with x read inside constant
    rw [read, constant, norm_one, mul_one]
    have moved : x / scale ∈ symmetricInterval q := by
      apply abs_le.mp
      rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
      have bounded := abs_le.mpr inside
      nlinarith
    rw [countingRaw, indicator_of_mem moved, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    exact (mul_le_mul_of_nonneg_left (pointwise x inside) (inv_nonneg.mpr positive.le)).trans_eq (by ring)
  have constantBound : ‖intervalConstant q‖ ≤ (1 : ℝ) := by
    have square : ‖intervalConstant q‖ ^ 2 = 2 * q := by
      exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
    norm_num at square
    nlinarith [norm_nonneg (intervalConstant q)]
  exact compared.trans (by nlinarith [mul_nonneg nonnegative (pow_nonneg (inv_nonneg.mpr positive.le) 3)])

theorem forcing_window_norm_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    ‖countingWindow scale (ForcingTail.forcingRemainderState coordinate)‖ ≤
      (4 * ‖ForcingWhole.coefficient coordinate‖) * scale⁻¹ ^ 3 := by
  apply window_norm_bound _ _ (ForcingTail.forcingRemainderState_ae_raw coordinate)
    _ scale (by positivity) large
  intro x inside
  have positive : 0 < scale := zero_lt_one.trans_le large
  have moved : |x / scale| ≤ q := by
    rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]
    have bounded := abs_le.mpr inside
    nlinarith
  have squareBound : x ^ 2 ≤ 1 := by nlinarith [inside.1, inside.2]
  calc
    _ ≤ 4 * ‖ForcingWhole.coefficient coordinate‖ * (x / scale) ^ 2 :=
      ForcingTail.forcingRemainder_bound coordinate moved
    _ = (4 * ‖ForcingWhole.coefficient coordinate‖ * scale⁻¹ ^ 2) * x ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ _ := by
      exact (mul_le_mul_of_nonneg_left squareBound (by positivity)).trans_eq (mul_one _)

theorem smooth_window_norm_bound (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (large : 1 ≤ scale) :
    ‖countingWindow scale (smoothState coordinate)‖ ≤ returnMass coordinate * scale⁻¹ ^ 3 := by
  apply window_norm_bound _ _ (smoothState_ae_raw coordinate) _ scale
    (integral_nonneg (fun _ => norm_nonneg _)) large
  intro x inside
  simpa only [mul_comm, returnMass] using! smoothFourier_bound coordinate scale large (abs_le.mpr inside)

theorem window_channel (scale : ℝ) (state : BurnolQuarterIntervalL2) :
    countingWindow scale state = burnolQuarterRestriction
      (ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension state)) := by
  simp only [countingWindow, ContinuousChannels.channel, neg_one_mul, map_smul]

theorem window_continuousOn (state : BurnolQuarterIntervalL2) :
    ContinuousOn (fun scale : ℝ => countingWindow scale state) (Ioi 0) := by
  have regular : ContinuousOn (fun scale : ℝ => ContinuousChannels.channel (-1) scale
      (burnolQuarterZeroExtension state)) (Ioi 0) := by
    unfold ContinuousChannels.channel
    apply ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.inv₀
      (fun scale positive => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr positive).ne')).smul
    exact (burnolMultiplicativeDilation_stronglyContinuous _).comp_continuousOn
      ((Real.continuousOn_log.mono (fun _ positive => ne_of_gt positive)).const_mul (-1))
  simpa only [Function.comp_def, ← window_channel] using!
    burnolQuarterRestriction.continuous.comp_continuousOn regular

theorem window_integrable_local (upper : ℝ) (state : BurnolQuarterIntervalL2) :
    IntegrableOn (fun scale : ℝ => countingWindow scale state) (Ioc 0 upper) := by
  simpa only [← window_channel] using! burnolQuarterRestriction.integrable_comp
    (ContinuousChannels.channel_integrable (-1) upper (burnolQuarterZeroExtension state))

private theorem window_integrable_of_bound (state : BurnolQuarterIntervalL2) (bound : ℝ)
    (bounded : ∀ scale : ℝ, 1 ≤ scale → ‖countingWindow scale state‖ ≤ bound * scale⁻¹ ^ 3) :
    IntegrableOn (fun scale : ℝ => countingWindow scale state) (Ioi 0) := by
  have powers : IntegrableOn (fun scale : ℝ => scale⁻¹ ^ 3) (Ioi 1) := by
    simpa only [show (-3 : ℝ) = -(3 : ℕ) by norm_num,
      Real.rpow_neg_natCast, zpow_neg, zpow_natCast, inv_pow] using!
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1))
  have tail : IntegrableOn (fun scale : ℝ => countingWindow scale state) (Ioi 1) := by
    apply (powers.const_mul bound).mono'
      (((window_continuousOn state).mono (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
        measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with scale large
    exact bounded scale large.le
  have full := (window_integrable_local 1 state).union tail
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at full

private theorem window_summable_of_bound (state : BurnolQuarterIntervalL2) (bound : ℝ)
    (bounded : ∀ scale : ℝ, 1 ≤ scale → ‖countingWindow scale state‖ ≤ bound * scale⁻¹ ^ 3) :
    Summable (fun n : ℕ => countingWindow (n : ℝ) state) := by
  have powers : Summable (fun n : ℕ => (n : ℝ)⁻¹ ^ 3) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (3 : ℕ)))
  apply (powers.mul_left bound).of_norm_bounded
  intro n
  by_cases zero : n = 0
  · subst n
    simp [countingWindow]
  · exact bounded (n : ℝ) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr zero)

theorem forcing_window_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun scale : ℝ => countingWindow scale (ForcingTail.forcingRemainderState coordinate)) (Ioi 0) :=
  window_integrable_of_bound _ _ (forcing_window_norm_bound coordinate)

theorem smooth_window_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun scale : ℝ => countingWindow scale (smoothState coordinate)) (Ioi 0) :=
  window_integrable_of_bound _ _ (smooth_window_norm_bound coordinate)

theorem forcing_window_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun n : ℕ => countingWindow (n : ℝ) (ForcingTail.forcingRemainderState coordinate)) :=
  window_summable_of_bound _ _ (forcing_window_norm_bound coordinate)

theorem smooth_window_summable (coordinate : BurnolCompletedMellinCoordinate) :
    Summable (fun n : ℕ => countingWindow (n : ℝ) (smoothState coordinate)) :=
  window_summable_of_bound _ _ (smooth_window_norm_bound coordinate)

private theorem finite_window_eq (N : ℕ) (state : BurnolQuarterIntervalL2) :
    burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension state)) =
      (∑ n ∈ Finset.Ico 1 N, countingWindow (n : ℝ) state) -
        ∫ scale : ℝ in Ioc 0 (N : ℝ), countingWindow scale state := by
  unfold FiniteForcing.source ContinuousChannels.normalization
  rw [map_sub, map_sum, ← burnolQuarterRestriction.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) (N : ℝ) _)]
  simp only [Channels.sourceChannel, countingWindow, ContinuousChannels.channel, neg_one_mul, map_smul]

private theorem window_limit (state : BurnolQuarterIntervalL2)
    (integer : Summable (fun n : ℕ => countingWindow (n : ℝ) state))
    (continuous : IntegrableOn (fun scale : ℝ => countingWindow scale state) (Ioi 0)) :
    Tendsto (fun N : ℕ => burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension state))) atTop
      (𝓝 ((∑' n : ℕ, countingWindow (n : ℝ) state) - ∫ scale : ℝ in Ioi 0, countingWindow scale state)) := by
  have integerLimit : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 1 N, countingWindow (n : ℝ) state) atTop
      (𝓝 (∑' n : ℕ, countingWindow (n : ℝ) state)) := by
    apply integer.hasSum.tendsto_sum_nat.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N large
    rw [Finset.sum_Ico_eq_sub _ large]
    simp [countingWindow]
  have continuousLimit : Tendsto (fun N : ℕ => ∫ scale : ℝ in Ioc 0 (N : ℝ), countingWindow scale state) atTop
      (𝓝 (∫ scale : ℝ in Ioi 0, countingWindow scale state)) := by
    apply (intervalIntegral_tendsto_integral_Ioi 0 continuous (tendsto_natCast_atTop_atTop (R := ℝ))).congr'
    filter_upwards with N
    exact intervalIntegral.integral_of_le (Nat.cast_nonneg N)
  simp_rw [finite_window_eq]
  exact integerLimit.sub continuousLimit

theorem forcing_window_limit (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => burnolQuarterRestriction (FiniteForcing.source N
      (burnolQuarterZeroExtension (ForcingTail.forcingRemainderState coordinate)))) atTop
      (𝓝 ((∑' n : ℕ, countingWindow (n : ℝ) (ForcingTail.forcingRemainderState coordinate)) -
        ∫ scale : ℝ in Ioi 0, countingWindow scale (ForcingTail.forcingRemainderState coordinate))) :=
  window_limit _ (forcing_window_summable coordinate) (forcing_window_integrable coordinate)

theorem smooth_window_limit (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => burnolQuarterRestriction (FiniteForcing.source N
      (burnolQuarterZeroExtension (smoothState coordinate)))) atTop
      (𝓝 ((∑' n : ℕ, countingWindow (n : ℝ) (smoothState coordinate)) -
        ∫ scale : ℝ in Ioi 0, countingWindow scale (smoothState coordinate))) :=
  window_limit _ (smooth_window_summable coordinate) (smooth_window_integrable coordinate)

private theorem counting_add (scale : ℝ) (left right : BurnolQuarterIntervalL2) :
    countingWindow scale (left + right) = countingWindow scale left + countingWindow scale right := by
  simp only [countingWindow, map_add, smul_add]

private theorem counting_sub (scale : ℝ) (left right : BurnolQuarterIntervalL2) :
    countingWindow scale (left - right) = countingWindow scale left - countingWindow scale right := by
  simp only [countingWindow, map_sub, smul_sub]

private theorem counting_smul (scale : ℝ) (scalar : ℂ) (state : BurnolQuarterIntervalL2) :
    countingWindow scale (scalar • state) = scalar • countingWindow scale state := by
  simp only [countingWindow, map_smul, smul_smul]
  rw [mul_comm]

private theorem finite_window_add (N : ℕ) (left right : BurnolQuarterIntervalL2) :
    burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension (left + right))) =
      burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension left)) +
      burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension right)) := by
  rw [finite_window_eq, finite_window_eq, finite_window_eq]
  simp_rw [counting_add]
  rw [Finset.sum_add_distrib, integral_add (window_integrable_local (N : ℝ) left)
    (window_integrable_local (N : ℝ) right)]
  abel

private theorem finite_window_sub (N : ℕ) (left right : BurnolQuarterIntervalL2) :
    burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension (left - right))) =
      burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension left)) -
      burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension right)) := by
  rw [finite_window_eq, finite_window_eq, finite_window_eq]
  simp_rw [counting_sub]
  rw [Finset.sum_sub_distrib, integral_sub (window_integrable_local (N : ℝ) left)
    (window_integrable_local (N : ℝ) right)]
  abel

private theorem finite_window_smul (N : ℕ) (scalar : ℂ) (state : BurnolQuarterIntervalL2) :
    burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension (scalar • state))) =
      scalar • burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension state)) := by
  rw [finite_window_eq, finite_window_eq]
  simp_rw [counting_smul]
  rw [← Finset.smul_sum, integral_smul, smul_sub]

theorem original_finite_window_decomposition (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) :
    burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) =
      ForcingPrimitive.leadingCoefficient coordinate • burnolQuarterRestriction (FiniteForcing.source N
        (burnolQuarterZeroExtension (SingularCounting.powerL2 coordinate))) +
      burnolQuarterRestriction (FiniteForcing.source N
        (burnolQuarterZeroExtension (ForcingTail.forcingRemainderState coordinate))) +
      burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension (smoothState coordinate))) -
      (ForcingMeanZero.mean coordinate + burnolQuarterMeanCoefficient (smoothState coordinate)) •
        burnolQuarterRestriction (FiniteForcing.source N (burnolQuarterZeroExtension (intervalConstant q))) := by
  conv_lhs => rw [original_window_decomposition]
  rw [finite_window_sub, finite_window_add, finite_window_add, finite_window_smul, finite_window_smul]

/-- The original uncentered q-window has its complete strong limit. Its
generated constant coefficient multiplies both the harmonic constant and log. -/
theorem original_window_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => WindowCounting.windowSource N
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) atTop
      (𝓝 (((ForcingPrimitive.leadingCoefficient coordinate •
          (((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q) +
        ((∑' n : ℕ, countingWindow (n : ℝ) (ForcingTail.forcingRemainderState coordinate)) -
          ∫ scale : ℝ in Ioi 0, countingWindow scale (ForcingTail.forcingRemainderState coordinate))) +
        ((∑' n : ℕ, countingWindow (n : ℝ) (smoothState coordinate)) -
          ∫ scale : ℝ in Ioi 0, countingWindow scale (smoothState coordinate))) -
        (ForcingMeanZero.mean coordinate + burnolQuarterMeanCoefficient (smoothState coordinate)) •
          ((Real.eulerMascheroniConstant : ℂ) • intervalConstant q + SmallScaleLog.logL2))) := by
  have power := (WindowCounting.power_limit_zero coordinate zero).const_smul
    (ForcingPrimitive.leadingCoefficient coordinate)
  have constants := WindowCounting.constant_limit.const_smul
    (ForcingMeanZero.mean coordinate + burnolQuarterMeanCoefficient (smoothState coordinate))
  have full := ((power.add (forcing_window_limit coordinate)).add (smooth_window_limit coordinate)).sub constants
  apply full.congr'
  filter_upwards with N
  simpa only [WindowCounting.windowSource] using! (original_finite_window_decomposition coordinate N).symm

end
end OriginalRieszFinitePairing.CoPoisson.Ward.WholeSourceWindow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
