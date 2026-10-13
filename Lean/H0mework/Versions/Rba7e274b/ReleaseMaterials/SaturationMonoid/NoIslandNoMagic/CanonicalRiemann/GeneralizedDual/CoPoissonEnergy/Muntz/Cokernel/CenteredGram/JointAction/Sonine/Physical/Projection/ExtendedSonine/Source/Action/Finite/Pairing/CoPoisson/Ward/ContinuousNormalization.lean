import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Normalization
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ContinuousChannels

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

private def continuousSourceRaw (lower upper : ℝ) (f : ℝ → ℂ) (radius x : ℝ) : ℂ :=
  (radius : ℂ)⁻¹ *
    (f (|x / radius|⁻¹) * burnolReciprocalStepSourceRaw lower upper (x / radius))

private theorem continuousSourceRaw_scaled (lower upper radius x : ℝ) (f : ℝ → ℂ)
    (positive : 0 < radius) (nonzero : x ≠ 0) :
    continuousSourceRaw lower upper f radius x =
      ((|x| : ℝ) : ℂ)⁻¹ * (Ico lower upper).indicator f (radius / |x|) := by
  have reciprocal : |x / radius|⁻¹ = radius / |x| := by
    rw [abs_div, abs_of_pos positive, inv_div]
  unfold continuousSourceRaw burnolReciprocalStepSourceRaw
  rw [reciprocal]
  simp only [indicator_apply, mem_Ico]
  by_cases inside : lower ≤ radius / |x| ∧ radius / |x| < upper
  · rw [if_pos inside, if_pos inside, abs_div, abs_of_pos positive]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne',
      Complex.ofReal_ne_zero.mpr (abs_pos.mpr nonzero).ne']
  · rw [if_neg inside, if_neg inside, mul_zero, mul_zero, mul_zero]

private theorem continuousSourceRaw_integral (lower upper x : ℝ) (f : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (nonzero : x ≠ 0) :
    (∫ radius : ℝ in Ioc 0 (N : ℝ), continuousSourceRaw lower upper f radius x) =
      normalizationRaw lower upper f N x := by
  have xPositive := abs_pos.mpr nonzero
  rw [setIntegral_congr_fun measurableSet_Ioc (fun radius inside =>
    continuousSourceRaw_scaled lower upper radius x f inside.1 nonzero), integral_const_mul]
  have changeVariable := intervalIntegral.inv_smul_integral_comp_div
    ((Ico lower upper).indicator f) |x| (a := 0) (b := (N : ℝ))
  rw [intervalIntegral.integral_of_le (by positivity), zero_div,
    intervalIntegral.integral_of_le (by positivity)] at changeVariable
  rw [← Complex.ofReal_inv]
  change |x|⁻¹ • (∫ radius : ℝ in Ioc 0 (N : ℝ),
    (Ico lower upper).indicator f (radius / |x|)) = _
  rw [changeVariable, integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
  unfold normalizationRaw
  have integrand : (fun u : ℝ => if u * |x| < (N : ℝ) then f u else 0) =
      (Iio ((N : ℝ) / |x|)).indicator f := by
    ext u
    simp only [indicator_apply, mem_Iio, lt_div_iff₀ xPositive]
  rw [integrand, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  apply setIntegral_congr_set
  filter_upwards [volume.ae_ne lower, volume.ae_ne upper, volume.ae_ne ((N : ℝ) / |x|)]
    with u lowerNe upperNe cutNe
  change (u ∈ Ico lower upper ∩ Ioc 0 ((N : ℝ) / |x|)) =
    (u ∈ Iio ((N : ℝ) / |x|) ∩ Ioc lower upper)
  apply propext
  simp only [mem_inter_iff, mem_Ico, mem_Ioc, mem_Iio]
  constructor
  · rintro ⟨⟨lowerAt, upperAt⟩, _, cutAt⟩
    exact ⟨lt_of_le_of_ne cutAt cutNe, lt_of_le_of_ne lowerAt lowerNe.symm, upperAt.le⟩
  · rintro ⟨cutAt, lowerAt, upperAt⟩
    exact ⟨⟨lowerAt.le, lt_of_le_of_ne upperAt upperNe⟩, positive.trans lowerAt, cutAt.le⟩

private theorem continuousSourceRaw_measurable (lower upper : ℝ) (f : ℝ → ℂ)
    (measured : Measurable f) :
    Measurable (fun point : ℝ × ℝ => continuousSourceRaw lower upper f point.1 point.2) := by
  unfold continuousSourceRaw
  apply (by fun_prop : Measurable (fun point : ℝ × ℝ => (point.1 : ℂ)⁻¹)).mul
  apply (measured.comp (by fun_prop)).mul
  unfold burnolReciprocalStepSourceRaw
  have reciprocal : Measurable (fun point : ℝ × ℝ => |point.2 / point.1|⁻¹) := by fun_prop
  apply Measurable.ite
    ((measurableSet_le measurable_const reciprocal).inter
      (measurableSet_lt reciprocal measurable_const))
  · fun_prop
  · exact measurable_const

theorem continuous_sourceChannel_coeFn (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (radius : ℝ) (radiusPositive : 0 < radius) :
    (ContinuousChannels.channel (-1) radius
      (burnolWeightedReciprocalStepSource lower upper f f') : ℝ → ℂ) =ᵐ[volume]
        fun x => (radius : ℂ)⁻¹ *
          (f (|x / radius|⁻¹) * burnolReciprocalStepSourceRaw lower upper (x / radius)) := by
  have action : ContinuousChannels.channel (-1) radius
      (burnolWeightedReciprocalStepSource lower upper f f') =
        burnolSourceScalePrimitive (burnolWeightedReciprocalStepSource lower upper f f') radius⁻¹ := by
    simp only [ContinuousChannels.channel, burnolSourceScalePrimitive, neg_one_mul,
      Real.log_inv, Real.sqrt_inv]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change _ = (((Real.sqrt radius)⁻¹ : ℝ) : ℂ) • _
    rw [Complex.ofReal_inv]
  rw [action]
  have actual := burnolSourceScalePrimitive_coeFn
    (burnolWeightedReciprocalStepSource lower upper f f')
    (fun x => f (|x|⁻¹) * burnolReciprocalStepSourceRaw lower upper x)
    (weighted_source_coeFn lower upper f f' positive ordered derivative regular measured)
    radius⁻¹ (inv_pos.mpr radiusPositive)
  simpa only [Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using! actual

/-- The original continuous dilation integral computes the complete same-N compensation. -/
theorem continuous_normalization_coeFn (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (measuredSource : Measurable f) :
    (ContinuousChannels.normalization (N : ℝ)
      (burnolWeightedReciprocalStepSource lower upper f f') : ℝ → ℂ) =ᵐ[volume]
        normalizationRaw lower upper f N := by
  let family := fun radius : ℝ => ContinuousChannels.channel (-1) radius
    (burnolWeightedReciprocalStepSource lower upper f f')
  have reads : ∀ᵐ radius ∂volume.restrict (Ioc 0 (N : ℝ)),
      (family radius : ℝ → ℂ) =ᵐ[volume]
        fun x => continuousSourceRaw lower upper f radius x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact continuous_sourceChannel_coeFn lower upper f f' positive ordered derivative regular measured
      radius inside.1
  have actual := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc 0 (N : ℝ))) family
    (ContinuousChannels.channel_integrable (-1) (N : ℝ)
      (burnolWeightedReciprocalStepSource lower upper f f'))
    (fun point : ℝ × ℝ => continuousSourceRaw lower upper f point.1 point.2)
    (continuousSourceRaw_measurable lower upper f measuredSource) reads
  filter_upwards [actual, volume.ae_ne (0 : ℝ)] with x native nonzero
  exact native.trans (continuousSourceRaw_integral lower upper x f N positive nonzero)

theorem continuous_normalization_eq (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (measuredSource : Measurable f) :
    ContinuousChannels.normalization (N : ℝ) (burnolWeightedReciprocalStepSource lower upper f f') =
      normalizationL2 lower upper f N positive
        (fun u inside => (derivative u inside).continuousAt.continuousWithinAt) measuredSource := by
  apply Lp.ext
  exact (continuous_normalization_coeFn lower upper f f' N positive ordered derivative regular measured
    measuredSource).trans (normalization_coeFn lower upper f N positive
      (fun u inside => (derivative u inside).continuousAt.continuousWithinAt) measuredSource).symm

/-- Finite counting and continuous compensation are now operations on the same original seed. -/
theorem weighted_prefix_eq_finite_sub_continuous (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f')
    (measuredSource : Measurable f) :
    weightedPrefix lower upper f f' N =
      (∑ n ∈ Finset.Ico 1 N, Channels.sourceChannel n (burnolWeightedReciprocalStepSource lower upper f f')) -
        ContinuousChannels.normalization (N : ℝ) (burnolWeightedReciprocalStepSource lower upper f f') := by
  rw [weighted_prefix_eq_finite_sub_normalization lower upper f f' N positive ordered derivative regular
    measured measuredSource, continuous_normalization_eq lower upper f f' N positive ordered derivative regular
      measured measuredSource]

end
end OriginalRieszFinitePairing.CoPoisson.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
