import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedRaw
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Channels

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

/-- The continuous channels use exactly the same cutoff as the finite integer source. -/
def normalizationRaw (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∫ u : ℝ in Ioc lower upper, if u * |x| < (N : ℝ) then f u else 0

theorem normalizationRaw_measurable (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (measured : Measurable f) : Measurable (normalizationRaw lower upper f N) := by
  have joint : Measurable (fun point : ℝ × ℝ =>
      if point.1 * |point.2| < (N : ℝ) then f point.1 else 0) := by
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (measured.comp measurable_fst) measurable_const
  exact joint.stronglyMeasurable.integral_prod_left'.measurable

theorem normalizationRaw_bound (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (regular : ContinuousOn f (Icc lower upper)) (x : ℝ) :
    ‖normalizationRaw lower upper f N x‖ ≤ ∫ u : ℝ in Ioc lower upper, ‖f u‖ := by
  apply norm_integral_le_of_norm_le (regular.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  filter_upwards with u
  split_ifs <;> simp

theorem normalizationRaw_zero_tail (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (x : ℝ) (excluded : (N : ℝ) ≤ lower * |x|) :
    normalizationRaw lower upper f N x = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u inside
  apply if_neg
  exact not_lt.mpr (excluded.trans (mul_le_mul_of_nonneg_right inside.1.le (abs_nonneg x)))

/-- Compact support and the source integral bound pay the whole-axis L² obligation. -/
theorem normalization_memLp (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (regular : ContinuousOn f (Icc lower upper))
    (measured : Measurable f) : MemLp (normalizationRaw lower upper f N) 2 volume := by
  let bound := ∫ u : ℝ in Ioc lower upper, ‖f u‖
  have envelope : MemLp ((symmetricInterval ((N : ℝ) / lower)).indicator
      (fun _ : ℝ => (bound : ℂ))) 2 volume :=
    memLp_indicator_const 2 (measurableSet_symmetricInterval _) _
      (Or.inr (by simp [symmetricInterval]))
  apply envelope.mono (normalizationRaw_measurable lower upper f N measured).aestronglyMeasurable
  filter_upwards with x
  by_cases inside : x ∈ symmetricInterval ((N : ℝ) / lower)
  · rw [indicator_of_mem inside, Complex.norm_real, Real.norm_eq_abs]
    exact (normalizationRaw_bound lower upper f N regular x).trans (le_abs_self _)
  · rw [indicator_of_notMem inside, norm_zero,
      normalizationRaw_zero_tail lower upper f N x ?_, norm_zero]
    have outside : (N : ℝ) / lower ≤ |x| :=
      le_of_not_ge (fun h => inside (abs_le.mp h))
    exact (div_le_iff₀ positive).mp outside |>.trans_eq (mul_comm _ _)

def normalizationL2 (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (regular : ContinuousOn f (Icc lower upper))
    (measured : Measurable f) : BurnolL2 :=
  (normalization_memLp lower upper f N positive regular measured).toLp (normalizationRaw lower upper f N)

theorem normalization_coeFn (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (regular : ContinuousOn f (Icc lower upper))
    (measured : Measurable f) :
    (normalizationL2 lower upper f N positive regular measured : ℝ → ℂ) =ᵐ[volume]
      normalizationRaw lower upper f N :=
  (normalization_memLp lower upper f N positive regular measured).coeFn_toLp

theorem weighted_source_coeFn (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') :
    (burnolWeightedReciprocalStepSource lower upper f f' : ℝ → ℂ) =ᵐ[volume]
      fun x => f (|x|⁻¹) * burnolReciprocalStepSourceRaw lower upper x := by
  let family := fun u : ℝ => f' u • burnolReciprocalStepNativeSource lower u
  let raw := fun point : ℝ × ℝ =>
    f' point.1 * burnolReciprocalStepSourceRaw lower point.1 point.2
  have sourceRead (u : ℝ) (inside : lower ≤ u) :
      (burnolReciprocalStepNativeSource lower u : ℝ → ℂ) =ᵐ[volume]
        burnolReciprocalStepSourceRaw lower u := by
    rw [burnolReciprocalStepNativeSource_eq lower u positive inside]
    exact (burnolReciprocalStepSource_memLp lower u positive inside).coeFn_toLp
  have sourceContinuous : ContinuousOn (burnolReciprocalStepNativeSource lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitReciprocalPrimitiveL2).mono
      (fun _ inside => positive.trans_le inside.1)).sub continuousOn_const
  have familyIntegral : IntegrableOn family (Ioc lower upper) :=
    (regular.smul sourceContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have rawMeasured : Measurable raw := by
    apply (measured.comp measurable_fst).mul
    unfold burnolReciprocalStepSourceRaw
    have reciprocal : Measurable (fun point : ℝ × ℝ => |point.2|⁻¹) := by fun_prop
    apply Measurable.ite
      ((measurableSet_le measurable_const reciprocal).inter
        (measurableSet_lt reciprocal measurable_fst))
    · fun_prop
    · exact measurable_const
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      (family u : ℝ → ℂ) =ᵐ[volume] fun x => raw (u, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    filter_upwards [Lp.coeFn_smul (f' u) (burnolReciprocalStepNativeSource lower u),
      sourceRead u inside.1.le] with x smulAt rawAt
    change (f' u • burnolReciprocalStepNativeSource lower u : BurnolL2) x = _
    rw [smulAt]
    change f' u * burnolReciprocalStepNativeSource lower u x = _
    rw [rawAt]
  have integralRead := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc lower upper)) family familyIntegral raw rawMeasured familyRead
  unfold burnolWeightedReciprocalStepSource
  filter_upwards [Lp.coeFn_sub (f upper • burnolReciprocalStepNativeSource lower upper)
    (∫ u : ℝ in Ioc lower upper, family u),
    Lp.coeFn_smul (f upper) (burnolReciprocalStepNativeSource lower upper),
    sourceRead upper ordered, integralRead] with x differenceAt smulAt headAt integralAt
  change (f upper • burnolReciprocalStepNativeSource lower upper -
    ∫ u : ℝ in Ioc lower upper, family u : BurnolL2) x = _
  rw [differenceAt, Pi.sub_apply, smulAt]
  change f upper * burnolReciprocalStepNativeSource lower upper x -
    (∫ u : ℝ in Ioc lower upper, family u : BurnolL2) x = _
  rw [headAt, integralAt]
  exact burnolReciprocalStepRaw_weightedIntegral lower upper x f f' derivative regular

theorem weighted_sourceChannel_coeFn (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (n : ℕ) (indexPositive : 0 < n) :
    (Channels.sourceChannel n (burnolWeightedReciprocalStepSource lower upper f f') : ℝ → ℂ) =ᵐ[volume]
      Channels.sourceChannelRaw lower upper f n := by
  have nonzero : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast indexPositive.ne')
  have pulled := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) nonzero).ae
    (weighted_source_coeFn lower upper f f' positive ordered derivative regular measured)
  have sourceAt : (fun x => burnolWeightedReciprocalStepSource lower upper f f' (x / (n : ℝ))) =ᵐ[volume]
      fun x => f (|x / (n : ℝ)|⁻¹) * burnolReciprocalStepSourceRaw lower upper (x / (n : ℝ)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using! pulled
  filter_upwards [Channels.sourceChannel_coeFn n indexPositive
    (burnolWeightedReciprocalStepSource lower upper f f'), sourceAt] with x channelAt seedAt
  rw [channelAt, seedAt]
  rfl

private theorem finite_source_count (lower upper x : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (nonzero : x ≠ 0) :
    (∑ n ∈ Finset.Ico 1 N, Channels.sourceChannelRaw lower upper f n x) =
      (∑ n ∈ Prefix.prefixChannels lower upper N x, f ((n : ℝ) / |x|)) *
        ((|x| : ℝ) : ℂ)⁻¹ := by
  classical
  have positiveIndex : 0 < ⌈lower * |x|⌉₊ :=
    Nat.ceil_pos.mpr (mul_pos positive (abs_pos.mpr nonzero))
  have activeSet : (Finset.Ico 1 N).filter
      (fun n => n ∈ burnolReciprocalStepChannels lower upper x) = Prefix.prefixChannels lower upper N x := by
    ext n
    simp only [Prefix.prefixChannels, burnolReciprocalStepChannels, Finset.mem_filter, Finset.mem_Ico]
    omega
  calc
    _ = ∑ n ∈ Finset.Ico 1 N, if n ∈ burnolReciprocalStepChannels lower upper x then
        f ((n : ℝ) / |x|) * ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro n inside
      exact Channels.sourceChannelRaw_count lower upper x f n
        (Nat.lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Ico.mp inside).1) nonzero
    _ = ∑ n ∈ Prefix.prefixChannels lower upper N x,
        f ((n : ℝ) / |x|) * ((|x| : ℝ) : ℂ)⁻¹ := by rw [← activeSet, Finset.sum_filter]
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The finite L² prefix contains precisely the integer source channels and
the continuous channels of the same N. -/
theorem weighted_prefix_eq_finite_sub_normalization (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (measuredSource : Measurable f) :
    weightedPrefix lower upper f f' N =
      (∑ n ∈ Finset.Ico 1 N, Channels.sourceChannel n (burnolWeightedReciprocalStepSource lower upper f f')) -
        normalizationL2 lower upper f N positive
          (fun u inside => (derivative u inside).continuousAt.continuousWithinAt) measuredSource := by
  classical
  let seed := burnolWeightedReciprocalStepSource lower upper f f'
  have channels : ∀ᵐ x : ℝ ∂volume, ∀ n : {n : ℕ // n ∈ Finset.Ico 1 N},
      Channels.sourceChannel n.1 seed x = Channels.sourceChannelRaw lower upper f n.1 x := by
    apply ae_all_iff.mpr
    intro n
    exact weighted_sourceChannel_coeFn lower upper f f' positive ordered derivative regular measured n.1
      (Nat.lt_of_lt_of_le (by decide : 0 < 1) (Finset.mem_Ico.mp n.2).1)
  apply Lp.ext
  filter_upwards [weighted_prefix_coeFn lower upper f f' N positive ordered derivative regular measured,
    Lp.coeFn_sub (∑ n ∈ Finset.Ico 1 N, Channels.sourceChannel n seed)
      (normalizationL2 lower upper f N positive
        (fun u inside => (derivative u inside).continuousAt.continuousWithinAt) measuredSource),
    Lp.coeFn_fun_finsetSum (Finset.Ico 1 N) (fun n => Channels.sourceChannel n seed),
    normalization_coeFn lower upper f N positive
      (fun u inside => (derivative u inside).continuousAt.continuousWithinAt) measuredSource,
    channels, volume.ae_ne (0 : ℝ)] with x prefixAt differenceAt sumAt normalizationAt channelAt nonzero
  rw [prefixAt, differenceAt, Pi.sub_apply, sumAt, normalizationAt]
  have finiteAt : (∑ n ∈ Finset.Ico 1 N, Channels.sourceChannel n seed x) =
      ∑ n ∈ Finset.Ico 1 N, Channels.sourceChannelRaw lower upper f n x := by
    apply Finset.sum_congr rfl
    intro n inside
    exact channelAt ⟨n, inside⟩
  change weightedPrefixRaw lower upper f N x = _
  rw [finiteAt, finite_source_count lower upper x f N positive nonzero]
  rfl

theorem normalization_pairing (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (regular : ContinuousOn f (Icc lower upper))
    (measured : Measurable f) (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x) (normalizationRaw lower upper f N x)) ∧
      inner ℂ test (normalizationL2 lower upper f N positive regular measured) =
        ∫ x : ℝ, inner ℂ (test x) (normalizationRaw lower upper f N x) := by
  have represents := normalization_coeFn lower upper f N positive regular measured
  constructor
  · exact (L2.integrable_inner (𝕜 := ℂ) test _).congr
      (represents.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  · rw [L2.inner_def]
    exact integral_congr_ae (represents.mono (fun x hx => congrArg (inner ℂ (test x)) hx))

end
end OriginalRieszFinitePairing.CoPoisson.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
