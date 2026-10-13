import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.SingularCounting

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SmallScaleLog

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

private def windowAverage (state : BurnolQuarterIntervalL2) : BurnolQuarterIntervalL2 :=
  burnolQuarterRestriction (ContinuousChannels.normalization 1 (burnolQuarterZeroExtension state))

private theorem windowAverage_coeFn (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (measured : Measurable raw) (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    (windowAverage state : ℝ → ℂ) =ᵐ[μq]
      fun x => ∫ scale : ℝ in Ioc 0 1, InverseAction.countingRaw scale raw x := by
  let source := burnolQuarterZeroExtension state
  let extended := (symmetricInterval q).indicator raw
  have sourceRead : (source : ℝ → ℂ) =ᵐ[volume] extended := by
    have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp represents
    filter_upwards [burnolQuarterZeroExtension_coe state, localRead] with x extendedAt rawAt
    rw [extendedAt]
    by_cases inside : x ∈ symmetricInterval q
    · change _ = (symmetricInterval q).indicator raw x
      rw [indicator_of_mem inside, indicator_of_mem inside, rawAt inside]
    · simp only [extended, indicator_of_notMem inside]
  have scaleRead (scale : ℝ) (positive : 0 < scale) :
      (ContinuousChannels.channel (-1) scale source : ℝ → ℂ) =ᵐ[volume]
        fun x => InverseAction.countingRaw scale raw x := by
    have action : ContinuousChannels.channel (-1) scale source =
        burnolSourceScalePrimitive source scale⁻¹ := by
      simp only [ContinuousChannels.channel, burnolSourceScalePrimitive, neg_one_mul,
        Real.log_inv, Real.sqrt_inv]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      change _ = (((Real.sqrt scale)⁻¹ : ℝ) : ℂ) • _
      rw [Complex.ofReal_inv]
    rw [action]
    have actual := burnolSourceScalePrimitive_coeFn source extended sourceRead scale⁻¹ (inv_pos.mpr positive)
    simpa only [InverseAction.countingRaw, extended, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using! actual
  have joint : Measurable (fun point : ℝ × ℝ => InverseAction.countingRaw point.1 raw point.2) := by
    unfold InverseAction.countingRaw
    exact (by fun_prop : Measurable (fun point : ℝ × ℝ => (point.1 : ℂ)⁻¹)).mul
      ((measured.indicator (measurableSet_symmetricInterval q)).comp (by fun_prop))
  have actual := OriginalPaPhysicalGreen.source_l2_bochner_coeFn (volume.restrict (Ioc 0 (1 : ℝ)))
    (fun scale => ContinuousChannels.channel (-1) scale source)
    (ContinuousChannels.channel_integrable (-1) 1 source)
    (fun point : ℝ × ℝ => InverseAction.countingRaw point.1 raw point.2) joint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with scale inside
      exact scaleRead scale inside.1)
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
    (ContinuousChannels.normalization 1 source),
    ae_restrict_of_ae (s := symmetricInterval q) actual] with x restricted averaged
  exact restricted.trans averaged

private theorem scaled_window (scale x : ℝ) (positive : 0 < scale) :
    x / scale ∈ symmetricInterval q ↔ |x| / q ≤ scale := by
  change -q ≤ x / scale ∧ x / scale ≤ q ↔ _
  rw [← abs_le, abs_div, abs_of_pos positive, div_le_iff₀ positive,
    div_le_iff₀ (by norm_num : (0 : ℝ) < q)]
  rw [mul_comm q scale]

private theorem cutoff_integral (cut : ℝ) (positive : 0 < cut)
    (f : ℝ → ℂ) :
    (∫ scale : ℝ in Ioc 0 1, (Ici cut).indicator f scale) = ∫ scale : ℝ in Ioc cut 1, f scale := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have intersection : Ici cut ∩ Ioc 0 1 = Icc cut 1 := by
    ext scale
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨first, _, third⟩
      exact ⟨first, third⟩
    · rintro ⟨first, second⟩
      exact ⟨first, positive.trans_le first, second⟩
  rw [intersection, integral_Icc_eq_integral_Ioc]

def logRaw (x : ℝ) : ℂ := (Real.log (|x| / q) : ℝ)

private theorem constant_integral (x : ℝ) (inside : x ∈ symmetricInterval q) (nonzero : x ≠ 0) :
    (∫ scale : ℝ in Ioc 0 1, InverseAction.countingRaw scale (fun _ => (1 : ℂ)) x) = -logRaw x := by
  classical
  have cutPositive : 0 < |x| / q := div_pos (abs_pos.mpr nonzero) (by norm_num)
  have cutBounded : |x| / q ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < q), one_mul]
    exact abs_le.mpr inside
  have integrand : ∀ scale ∈ Ioc (0 : ℝ) 1,
      InverseAction.countingRaw scale (fun _ => (1 : ℂ)) x =
        (Ici (|x| / q)).indicator (fun scale : ℝ => (scale : ℂ)⁻¹) scale := by
    intro scale scaleInside
    unfold InverseAction.countingRaw
    rw [indicator_apply, indicator_apply]
    simp only [scaled_window scale x scaleInside.1,
      mem_Ici, mul_ite, mul_one, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioc integrand, cutoff_integral _ cutPositive,
    ← intervalIntegral.integral_of_le cutBounded]
  simp only [← Complex.ofReal_inv, intervalIntegral.integral_ofReal]
  rw [show (fun scale : ℝ => scale⁻¹) = (fun scale => 1 / scale) by ext; simp,
    integral_one_div_of_pos cutPositive zero_lt_one, one_div, Real.log_inv]
  simp only [logRaw, Complex.ofReal_neg]

private theorem constant_average_read :
    (windowAverage (intervalConstant q) : ℝ → ℂ) =ᵐ[μq] fun x => -logRaw x := by
  filter_upwards [windowAverage_coeFn (intervalConstant q) (fun _ => (1 : ℂ)) measurable_const
    (intervalConstant_coeFn q), ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))] with x averaged inside nonzero
  exact averaged.trans (constant_integral x inside nonzero)

/-- The original continuous source integral supplies the real logarithm's L² witness. -/
theorem log_memLp : MemLp logRaw 2 μq := by
  have source := (Lp.memLp (windowAverage (intervalConstant q))).ae_eq constant_average_read
  have result := source.neg
  change MemLp (fun x => -(-logRaw x)) 2 μq at result
  simpa only [neg_neg] using result

def logL2 : BurnolQuarterIntervalL2 := log_memLp.toLp logRaw

theorem log_coeFn : (logL2 : ℝ → ℂ) =ᵐ[μq] logRaw := log_memLp.coeFn_toLp

def centeredLog : BurnolQuarterMeanZeroCarrier := Constructor.zeroMean logL2

private theorem constant_average : windowAverage (intervalConstant q) = -logL2 := by
  apply Lp.ext
  exact constant_average_read.trans ((Lp.coeFn_neg logL2).trans log_coeFn.neg).symm

private theorem power_counting_raw (coordinate : BurnolCompletedMellinCoordinate)
    (scale x : ℝ) (positive : 0 < scale) :
    InverseAction.countingRaw scale (SingularCounting.powerRaw coordinate) x =
      (Ici (|x| / q)).indicator
        (fun scale : ℝ => (scale : ℂ) ^ (-star coordinate.value) * SingularCounting.powerRaw coordinate x) scale := by
  classical
  unfold InverseAction.countingRaw
  rw [indicator_apply, indicator_apply]
  simp only [scaled_window scale x positive, mem_Ici]
  by_cases inside : |x| / q ≤ scale
  · rw [if_pos inside, if_pos inside]
    unfold SingularCounting.powerRaw
    have scaleNe : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
    have powerNe : (scale : ℂ) ^ star coordinate.value ≠ 0 := by simp [scaleNe]
    rw [abs_div, abs_of_pos positive, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg (abs_nonneg x) positive.le,
      Complex.cpow_sub _ _ scaleNe, cpow_one, cpow_neg]
    field_simp [scaleNe, powerNe]
  · rw [if_neg inside, if_neg inside, mul_zero]

private theorem power_integral (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (inside : x ∈ symmetricInterval q) (nonzero : x ≠ 0) :
    (∫ scale : ℝ in Ioc 0 1, InverseAction.countingRaw scale (SingularCounting.powerRaw coordinate) x) =
      (1 / (1 - star coordinate.value)) * SingularCounting.powerRaw coordinate x -
        (q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value) := by
  have cutPositive : 0 < |x| / q := div_pos (abs_pos.mpr nonzero) (by norm_num)
  have cutBounded : |x| / q ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < q), one_mul]
    exact abs_le.mpr inside
  have exponent : -1 < (-star coordinate.value).re := by
    simpa only [neg_re, star_def, conj_re] using neg_lt_neg coordinate.belowOne
  rw [setIntegral_congr_fun measurableSet_Ioc (fun scale scaleInside =>
      power_counting_raw coordinate scale x scaleInside.1), cutoff_integral _ cutPositive,
    integral_mul_const, ← intervalIntegral.integral_of_le cutBounded,
    integral_cpow (Or.inl exponent), show -star coordinate.value + 1 = 1 - star coordinate.value by ring,
    Complex.ofReal_one, one_cpow]
  have endpoint : (((|x| / q : ℝ) : ℂ) ^ (1 - star coordinate.value)) *
      SingularCounting.powerRaw coordinate x = (q : ℂ) ^ (star coordinate.value - 1) := by
    unfold SingularCounting.powerRaw
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg (abs_nonneg x) (by norm_num),
      div_mul_eq_mul_div, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_pos.mpr nonzero).ne'),
      show (1 - star coordinate.value) + (star coordinate.value - 1) = 0 by ring,
      cpow_zero, one_div, ← cpow_neg]
    congr 1
    ring
  calc
    _ = (1 / (1 - star coordinate.value)) * SingularCounting.powerRaw coordinate x -
        ((((|x| / q : ℝ) : ℂ) ^ (1 - star coordinate.value)) *
          SingularCounting.powerRaw coordinate x) / (1 - star coordinate.value) := by ring
    _ = _ := by rw [endpoint]

private theorem power_average (coordinate : BurnolCompletedMellinCoordinate) :
    windowAverage (SingularCounting.powerL2 coordinate) =
      (1 / (1 - star coordinate.value)) • SingularCounting.powerL2 coordinate -
        ((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q := by
  have measured : Measurable (SingularCounting.powerRaw coordinate) := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x outside
    exact (Complex.continuousAt_ofReal_cpow_const |x| (star coordinate.value - 1)
      (Or.inr (abs_ne_zero.mpr outside))).comp continuous_abs.continuousAt |>.continuousWithinAt
  apply Lp.ext
  filter_upwards [windowAverage_coeFn (SingularCounting.powerL2 coordinate) (SingularCounting.powerRaw coordinate)
    measured (SingularCounting.power_coeFn coordinate),
    Lp.coeFn_sub ((1 / (1 - star coordinate.value)) • SingularCounting.powerL2 coordinate)
      (((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q),
    Lp.coeFn_smul (1 / (1 - star coordinate.value)) (SingularCounting.powerL2 coordinate),
    Lp.coeFn_smul ((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) (intervalConstant q),
    SingularCounting.power_coeFn coordinate, intervalConstant_coeFn q,
    ae_restrict_mem (measurableSet_symmetricInterval q),
    ae_restrict_of_ae (s := symmetricInterval q) (volume.ae_ne (0 : ℝ))]
      with x averaged subAt powerAt constantAt rawAt oneAt inside nonzero
  rw [averaged, subAt, Pi.sub_apply, powerAt, constantAt]
  change _ = (1 / (1 - star coordinate.value)) * SingularCounting.powerL2 coordinate x -
    ((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) * intervalConstant q x
  rw [rawAt, oneAt, mul_one]
  exact power_integral coordinate x inside nonzero

theorem constant_normalization_window :
    burnolQuarterRestriction (ContinuousChannels.normalization 1
      (burnolQuarterZeroExtension (intervalConstant q))) = -logL2 :=
  constant_average

theorem power_normalization_window (coordinate : BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (ContinuousChannels.normalization 1
      (burnolQuarterZeroExtension (SingularCounting.powerL2 coordinate))) =
      (1 / (1 - star coordinate.value)) • SingularCounting.powerL2 coordinate -
        ((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q :=
  power_average coordinate

private theorem windowAverage_centered (state : BurnolQuarterIntervalL2) :
    windowAverage (Constructor.zeroMean state : BurnolQuarterIntervalL2) =
      windowAverage state - burnolQuarterMeanCoefficient state • windowAverage (intervalConstant q) := by
  have native : ContinuousChannels.normalization 1 (burnolQuarterZeroExtension
      (Constructor.zeroMean state : BurnolQuarterIntervalL2)) =
      ContinuousChannels.normalization 1 (burnolQuarterZeroExtension state) -
        burnolQuarterMeanCoefficient state •
          ContinuousChannels.normalization 1 (burnolQuarterZeroExtension (intervalConstant q)) := by
    unfold ContinuousChannels.normalization
    have integrand : ∀ scale : ℝ,
        ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension
          (Constructor.zeroMean state : BurnolQuarterIntervalL2)) =
        ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension state) -
          burnolQuarterMeanCoefficient state •
            ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension (intervalConstant q)) := by
      intro scale
      rw [Constructor.zeroMean_read]
      simp only [ContinuousChannels.channel, map_sub, map_smul, smul_sub, smul_smul]
      module
    have scaledIntegral := (ContinuousChannels.channel_integrable (-1) 1
      (burnolQuarterZeroExtension (intervalConstant q))).smul (burnolQuarterMeanCoefficient state)
    change IntegrableOn (fun scale => burnolQuarterMeanCoefficient state •
      ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension (intervalConstant q))) (Ioc 0 1)
      at scaledIntegral
    rw [setIntegral_congr_fun measurableSet_Ioc (fun scale _ => integrand scale),
      integral_sub (ContinuousChannels.channel_integrable (-1) 1 (burnolQuarterZeroExtension state))
        scaledIntegral, integral_smul]
  unfold windowAverage
  rw [native, map_sub, map_smul]

private theorem centered_average (state : BurnolQuarterMeanZeroCarrier) :
    (∫ scale : ℝ in Ioc 0 1, InverseAction.centeredCounting scale state) =
      Constructor.zeroMean (windowAverage (state : BurnolQuarterIntervalL2)) := by
  unfold windowAverage ContinuousChannels.normalization
  change _ = (Constructor.zeroMean.comp burnolQuarterRestriction)
    (∫ scale : ℝ in Ioc 0 1, ContinuousChannels.channel (-1) scale (burnolQuarterZeroExtension state))
  rw [← (Constructor.zeroMean.comp burnolQuarterRestriction).integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) 1 (burnolQuarterZeroExtension state))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro scale _
  simp only [InverseAction.centeredCounting, InverseAction.countingWindow, ContinuousChannels.channel,
    neg_one_mul, ContinuousLinearMap.comp_apply, map_smul]

/-- The original small-scale source gives precisely the original power mean
times the centered logarithm, with its computed negative sign. -/
theorem smallScaleResidual_eq_log (coordinate : BurnolCompletedMellinCoordinate) :
    SingularCounting.smallScaleResidual coordinate =
      (-burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate)) • centeredLog := by
  unfold SingularCounting.smallScaleResidual
  rw [centered_average, SingularCounting.centeredPower, windowAverage_centered, power_average,
    constant_average, map_sub, map_sub, map_smul, map_smul, Constructor.zeroMean_constant,
    smul_zero, sub_zero, map_smul, map_neg]
  change (1 / (1 - star coordinate.value)) • Constructor.zeroMean (SingularCounting.powerL2 coordinate) -
    ((1 / (1 - star coordinate.value)) • Constructor.zeroMean (SingularCounting.powerL2 coordinate) -
      burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate) • -centeredLog) = _
  module

theorem original_singular_log_limit (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N => SingularCounting.projectedSource N (SingularCounting.originalSingularSource coordinate)) atTop
      (𝓝 (-(ForcingPrimitive.leadingCoefficient coordinate *
        burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate)) • centeredLog)) := by
  simpa only [smallScaleResidual_eq_log, smul_smul, mul_neg] using
    SingularCounting.original_singular_limit coordinate zero

private theorem centered_constant_channel (scale : ℝ) (large : 1 ≤ scale) :
    Constructor.zeroMean (InverseAction.countingWindow scale (intervalConstant q)) = 0 := by
  have same : InverseAction.countingWindow scale (intervalConstant q) =
      (scale : ℂ)⁻¹ • intervalConstant q := by
    apply Lp.ext
    filter_upwards [InverseAction.countingWindow_raw scale (zero_lt_one.trans_le large)
      (intervalConstant q) (fun _ => (1 : ℂ)) (intervalConstant_coeFn q),
      Lp.coeFn_smul (scale : ℂ)⁻¹ (intervalConstant q), intervalConstant_coeFn q,
      ae_restrict_mem (measurableSet_symmetricInterval q)] with x counted scaled constant inside
    rw [counted, scaled]
    have scaledInside : x / scale ∈ symmetricInterval q := (scaled_window scale x
      (zero_lt_one.trans_le large)).mpr
        ((by rw [div_le_iff₀ (by norm_num : (0 : ℝ) < q), one_mul]; exact abs_le.mpr inside :
          |x| / q ≤ 1).trans large)
    change InverseAction.countingRaw scale (fun _ => (1 : ℂ)) x = (scale : ℂ)⁻¹ * intervalConstant q x
    rw [constant]
    unfold InverseAction.countingRaw
    rw [indicator_of_mem scaledInside]
  rw [same, map_smul, Constructor.zeroMean_constant, smul_zero]

/-- An uncentered constant seed produces the same positive centered log
at every finite cutoff N ≥ 1; its low-scale mean defect is retained. -/
theorem constant_projected_source (N : ℕ) (positive : 0 < N) :
    Constructor.zeroMean (burnolQuarterRestriction
      (FiniteForcing.source N (burnolQuarterZeroExtension (intervalConstant q)))) = centeredLog := by
  let projection := Constructor.zeroMean.comp burnolQuarterRestriction
  let source := burnolQuarterZeroExtension (intervalConstant q)
  have largeRead (scale : ℝ) (large : 1 ≤ scale) :
      projection (ContinuousChannels.channel (-1) scale source) = 0 := by
    have read := centered_constant_channel scale large
    simpa only [projection, source, ContinuousLinearMap.comp_apply, ContinuousChannels.channel,
      InverseAction.countingWindow, neg_one_mul, map_smul] using read
  have integers : (∑ n ∈ Finset.Ico 1 N, projection (Channels.sourceChannel n source)) = 0 := by
    apply Finset.sum_eq_zero
    intro n inside
    simpa only [Channels.sourceChannel, ContinuousChannels.channel, neg_one_mul] using
      largeRead n (by exact_mod_cast (Finset.mem_Ico.mp inside).1)
  have wholeIntegral := projection.integrable_comp (ContinuousChannels.channel_integrable (-1) N source)
  change IntegrableOn (fun scale => projection (ContinuousChannels.channel (-1) scale source))
    (Ioc 0 (N : ℝ)) at wholeIntegral
  have after : (1 : ℝ) ≤ N := by exact_mod_cast positive
  have largeZero : (∫ scale : ℝ in Ioc 1 (N : ℝ),
      projection (ContinuousChannels.channel (-1) scale source)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun scale inside => largeRead scale inside.1.le)
  have continuous : projection (ContinuousChannels.normalization N source) = -centeredLog := by
    unfold ContinuousChannels.normalization
    rw [← projection.integral_comp_comm (ContinuousChannels.channel_integrable (-1) N source),
      ← Ioc_union_Ioc_eq_Ioc zero_le_one after,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (wholeIntegral.mono_set (Ioc_subset_Ioc le_rfl after))
        (wholeIntegral.mono_set (Ioc_subset_Ioc zero_le_one le_rfl)),
      largeZero, add_zero,
      projection.integral_comp_comm (ContinuousChannels.channel_integrable (-1) 1 source)]
    change Constructor.zeroMean (windowAverage (intervalConstant q)) = -centeredLog
    rw [constant_average, map_neg]
    rfl
  change projection (FiniteForcing.source N source) = _
  unfold FiniteForcing.source
  rw [map_sub, map_sum, integers, continuous, zero_sub, neg_neg]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SmallScaleLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
