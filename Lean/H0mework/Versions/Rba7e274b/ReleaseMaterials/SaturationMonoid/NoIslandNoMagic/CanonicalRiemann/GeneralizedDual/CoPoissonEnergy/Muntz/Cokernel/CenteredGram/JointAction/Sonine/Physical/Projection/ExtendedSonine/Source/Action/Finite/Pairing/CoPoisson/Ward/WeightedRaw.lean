import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WeightedPrefix
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Arithmetic
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
noncomputable section

def weightedPrefixRaw (lower upper : ℝ) (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ n ∈ Prefix.prefixChannels lower upper N x, f ((n : ℝ) / |x|)) *
    ((|x| : ℝ) : ℂ)⁻¹ - ∫ u : ℝ in Ioc lower upper, if u * |x| < (N : ℝ) then f u else 0

private theorem prefixChannels_clipped (lower upper x : ℝ) (N : ℕ)
    (nonzero : x ≠ 0) (included : lower * |x| ≤ (N : ℝ)) :
    Prefix.prefixChannels lower upper N x =
      burnolReciprocalStepChannels lower (min upper ((N : ℝ) / |x|)) x := by
  rw [Prefix.prefixChannels_eq]
  unfold burnolReciprocalStepChannels
  rw [min_eq_left (Nat.ceil_le.mpr included)]
  congr 1
  by_cases upperIn : upper ≤ (N : ℝ) / |x|
  · rw [min_eq_left upperIn, min_eq_left (Nat.ceil_le.mpr
      ((le_div_iff₀ (abs_pos.mpr nonzero)).mp upperIn))]
  · rw [min_eq_right (le_of_not_ge upperIn), div_mul_cancel₀ _ (abs_pos.mpr nonzero).ne',
      Nat.ceil_natCast, min_eq_right]
    exact_mod_cast (le_of_not_ge ((le_div_iff₀ (abs_pos.mpr nonzero)).not.mp upperIn)).trans
      (Nat.le_ceil (upper * |x|))

private theorem prefix_clipped (lower upper x : ℝ) (N : ℕ)
    (nonzero : x ≠ 0) (included : lower * |x| ≤ (N : ℝ)) :
    Prefix.prefixRaw lower upper N x =
      burnolReciprocalStepWaveRaw lower (min upper ((N : ℝ) / |x|)) x := by
  unfold Prefix.prefixRaw Prefix.prefixReal
  rw [if_neg nonzero, prefixChannels_clipped lower upper x N nonzero included,
    min_eq_left included]
  unfold burnolReciprocalStepWaveRaw burnolReciprocalStepWaveReal
  rw [if_neg nonzero]
  congr 1
  have clipped : min (upper * |x|) (N : ℝ) = min upper ((N : ℝ) / |x|) * |x| := by
    rw [min_mul_of_nonneg _ _ (abs_nonneg x), div_mul_cancel₀ _ (abs_pos.mpr nonzero).ne']
  rw [clipped]
  field_simp

private theorem clipped_mean (lower upper x : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (nonzero : x ≠ 0) :
    (∫ u : ℝ in Ioc lower upper, if u * |x| < (N : ℝ) then f u else 0) =
      ∫ u : ℝ in Ioc lower (min upper ((N : ℝ) / |x|)), f u := by
  have expression : (fun u : ℝ => if u * |x| < (N : ℝ) then f u else 0) =
      (Iio ((N : ℝ) / |x|)).indicator f := by
    ext u
    simp only [indicator_apply, mem_Iio, lt_div_iff₀ (abs_pos.mpr nonzero)]
  rw [expression, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  apply setIntegral_congr_set
  filter_upwards [volume.ae_ne ((N : ℝ) / |x|)] with u distinct
  change (u ∈ Iio ((N : ℝ) / |x|) ∩ Ioc lower upper) =
    (u ∈ Ioc lower (min upper ((N : ℝ) / |x|)))
  apply propext
  simp only [mem_inter_iff, mem_Iio, mem_Ioc, le_min_iff]
  constructor
  · rintro ⟨first, second, third⟩
    exact ⟨second, third, first.le⟩
  · rintro ⟨first, second, third⟩
    exact ⟨lt_of_le_of_ne third distinct, first, second⟩

private theorem weightedPrefixRaw_clipped (lower upper x : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (nonzero : x ≠ 0) (included : lower * |x| ≤ (N : ℝ)) :
    weightedPrefixRaw lower upper f N x =
      Arithmetic.weightedCountingRaw lower (min upper ((N : ℝ) / |x|)) f x := by
  unfold weightedPrefixRaw Arithmetic.weightedCountingRaw
  rw [prefixChannels_clipped lower upper x N nonzero included, clipped_mean lower upper x N f nonzero]

private theorem prefix_family_measurable (lower : ℝ) (f' : ℝ → ℂ) (N : ℕ)
    (measured : Measurable f') :
    Measurable (fun point : ℝ × ℝ => f' point.1 * Prefix.prefixRaw lower point.1 N point.2) := by
  apply (measured.comp measurable_fst).mul
  unfold Prefix.prefixRaw Prefix.prefixReal
  simp only [Prefix.prefixChannels_eq, Nat.card_Ico]
  apply Complex.measurable_ofReal.comp
  apply Measurable.ite (measurable_snd (measurableSet_singleton (0 : ℝ)))
  · fun_prop
  · fun_prop

private theorem prefix_scalar_integrable (lower upper x : ℝ) (N : ℕ) (f' : ℝ → ℂ)
    (positive : 0 < lower) (nonzero : x ≠ 0)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') :
    IntegrableOn (fun u => f' u * Prefix.prefixRaw lower u N x) (Ioc lower upper) := by
  apply ((regular.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mul_const |x|⁻¹).mono'
    (((prefix_family_measurable lower f' N measured).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
  change ‖f' u * Prefix.prefixRaw lower u N x‖ ≤ ‖f' u‖ * |x|⁻¹
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (Prefix.prefix_bound lower u N x positive inside.1.le nonzero) (norm_nonneg _)

private theorem weightedPrefixRaw_zero_tail (lower upper x : ℝ) (N : ℕ) (f : ℝ → ℂ)
    (nonzero : x ≠ 0) (ordered : lower ≤ upper) (excluded : (N : ℝ) ≤ lower * |x|) :
    weightedPrefixRaw lower upper f N x = 0 := by
  have lowerIndex : N ≤ ⌈lower * |x|⌉₊ :=
    by exact_mod_cast excluded.trans (Nat.le_ceil (lower * |x|))
  have upperIndex : N ≤ ⌈upper * |x|⌉₊ := by
    exact_mod_cast (excluded.trans (mul_le_mul_of_nonneg_right ordered (abs_nonneg x))).trans
      (Nat.le_ceil (upper * |x|))
  unfold weightedPrefixRaw
  rw [Prefix.prefixChannels_eq, min_eq_right lowerIndex, min_eq_right upperIndex]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_mul, zero_sub]
  rw [clipped_mean lower upper x N f nonzero]
  have empty : Ioc lower (min upper ((N : ℝ) / |x|)) = ∅ :=
    Ioc_eq_empty_of_le ((min_le_right _ _).trans
      ((div_le_iff₀ (abs_pos.mpr nonzero)).mpr excluded))
  simp [empty]

/-- The finite primitive's weighted algorithm calculates both its integer
channels and its own continuous compensation, eliminating the derivative. -/
theorem weighted_prefix_raw (lower upper x : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper) (nonzero : x ≠ 0)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') :
    f upper * Prefix.prefixRaw lower upper N x -
      (∫ u : ℝ in Ioc lower upper, f' u * Prefix.prefixRaw lower u N x) =
        weightedPrefixRaw lower upper f N x := by
  by_cases excluded : (N : ℝ) ≤ lower * |x|
  · rw [weightedPrefixRaw_zero_tail lower upper x N f nonzero ordered excluded,
      Prefix.prefix_eq_zero_tail lower upper N x ordered excluded, mul_zero]
    rw [setIntegral_eq_zero_of_forall_eq_zero (fun u inside => by
      rw [Prefix.prefix_eq_zero_tail lower u N x inside.1.le excluded, mul_zero]), sub_zero]
  have lowerIn := le_of_not_ge excluded
  by_cases upperIn : upper * |x| ≤ (N : ℝ)
  · rw [Prefix.prefix_eq_wave lower upper N x positive ordered nonzero upperIn,
      weightedPrefixRaw_clipped lower upper x N f nonzero lowerIn,
      min_eq_left ((le_div_iff₀ (abs_pos.mpr nonzero)).mpr upperIn)]
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u inside =>
      congrArg (f' u * ·) (Prefix.prefix_eq_wave lower u N x positive inside.1.le nonzero
        ((mul_le_mul_of_nonneg_right inside.2 (abs_nonneg x)).trans upperIn)))]
    exact Arithmetic.weighted_count_raw lower upper x f f' positive ordered nonzero derivative regular
  let cut := (N : ℝ) / |x|
  have lowerCut : lower ≤ cut := (le_div_iff₀ (abs_pos.mpr nonzero)).mpr lowerIn
  have cutUpper : cut ≤ upper := (div_le_iff₀ (abs_pos.mpr nonzero)).mpr (le_of_not_ge upperIn)
  have wholeIntegral := prefix_scalar_integrable lower upper x N f' positive nonzero regular measured
  have split : (∫ u : ℝ in Ioc lower upper, f' u * Prefix.prefixRaw lower u N x) =
      (∫ u : ℝ in Ioc lower cut, f' u * Prefix.prefixRaw lower u N x) +
        ∫ u : ℝ in Ioc cut upper, f' u * Prefix.prefixRaw lower u N x := by
    rw [← Ioc_union_Ioc_eq_Ioc lowerCut cutUpper]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (wholeIntegral.mono_set (Ioc_subset_Ioc le_rfl cutUpper))
      (wholeIntegral.mono_set (Ioc_subset_Ioc lowerCut le_rfl))
  have front : (∫ u : ℝ in Ioc lower cut, f' u * Prefix.prefixRaw lower u N x) =
      ∫ u : ℝ in Ioc lower cut, f' u * burnolReciprocalStepWaveRaw lower u x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u inside
    change f' u * Prefix.prefixRaw lower u N x = f' u * burnolReciprocalStepWaveRaw lower u x
    rw [Prefix.prefix_eq_wave lower u N x positive inside.1.le nonzero
      ((le_div_iff₀ (abs_pos.mpr nonzero)).mp inside.2)]
  have tail : (∫ u : ℝ in Ioc cut upper, f' u * Prefix.prefixRaw lower u N x) =
      (f upper - f cut) * burnolReciprocalStepWaveRaw lower cut x := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u inside =>
      congrArg (f' u * ·) (by
        rw [prefix_clipped lower u x N nonzero lowerIn, min_eq_right inside.1.le])),
      integral_mul_const, ← intervalIntegral.integral_of_le cutUpper]
    congr 1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u inside => derivative u (Icc_subset_Icc lowerCut le_rfl
        (by simpa only [uIcc_of_le cutUpper] using inside)))
      ((regular.mono (Icc_subset_Icc lowerCut le_rfl)).intervalIntegrable_of_Icc cutUpper)
  rw [split, front, tail, prefix_clipped lower upper x N nonzero lowerIn,
    weightedPrefixRaw_clipped lower upper x N f nonzero lowerIn,
    min_eq_right cutUpper]
  have original := Arithmetic.weighted_count_raw lower cut x f f' positive lowerCut nonzero
    (fun u inside => derivative u (Icc_subset_Icc le_rfl cutUpper inside))
    (regular.mono (Icc_subset_Icc le_rfl cutUpper))
  linear_combination original

/-- The finite L² source has the computed, derivative-free counting representative. -/
theorem weighted_prefix_coeFn (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') :
    (weightedPrefix lower upper f f' N : ℝ → ℂ) =ᵐ[volume] weightedPrefixRaw lower upper f N := by
  let family := fun u : ℝ => f' u • Prefix.prefixL2 lower u N
  let raw := fun point : ℝ × ℝ => f' point.1 * Prefix.prefixRaw lower point.1 N point.2
  have familyIntegral : IntegrableOn family (Ioc lower upper) :=
    (regular.smul ((Prefix.prefix_continuous_upper lower N).mono
      (fun _ inside => positive.trans_le inside.1))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      (family u : ℝ → ℂ) =ᵐ[volume] fun x => raw (u, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    filter_upwards [Lp.coeFn_smul (f' u) (Prefix.prefixL2 lower u N),
      Prefix.prefix_coeFn lower u N positive inside.1.le] with x smulAt rawAt
    change (f' u • Prefix.prefixL2 lower u N : BurnolL2) x = _
    rw [smulAt]
    change f' u * Prefix.prefixL2 lower u N x = _
    rw [rawAt]
  have integralRead := OriginalPaPhysicalGreen.source_l2_bochner_coeFn
    (volume.restrict (Ioc lower upper)) family familyIntegral raw
    (prefix_family_measurable lower f' N measured) familyRead
  rw [weightedPrefix_eq_program]
  filter_upwards [Lp.coeFn_sub (f upper • Prefix.prefixL2 lower upper N)
    (∫ u : ℝ in Ioc lower upper, family u),
    Lp.coeFn_smul (f upper) (Prefix.prefixL2 lower upper N),
    Prefix.prefix_coeFn lower upper N positive ordered, integralRead,
    volume.ae_ne (0 : ℝ)] with x differenceAt smulAt headAt integralAt nonzero
  change (f upper • Prefix.prefixL2 lower upper N -
    ∫ u : ℝ in Ioc lower upper, family u : BurnolL2) x = _
  rw [differenceAt, Pi.sub_apply, smulAt]
  change f upper * Prefix.prefixL2 lower upper N x -
    (∫ u : ℝ in Ioc lower upper, family u : BurnolL2) x = _
  rw [headAt, integralAt]
  exact weighted_prefix_raw lower upper x f f' N positive ordered nonzero derivative regular measured

theorem weighted_prefix_pairing (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    inner ℂ test (weightedPrefix lower upper f f' N) =
      ∫ x : ℝ, inner ℂ (test x) (weightedPrefixRaw lower upper f N x) := by
  rw [L2.inner_def]
  exact integral_congr_ae ((weighted_prefix_coeFn lower upper f f' N positive ordered
    derivative regular measured).mono (fun x hx => congrArg (inner ℂ (test x)) hx))

theorem weighted_prefix_pairing_left (lower upper : ℝ) (f f' : ℝ → ℂ) (N : ℕ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    inner ℂ (weightedPrefix lower upper f f' N) test =
      ∫ x : ℝ, inner ℂ (weightedPrefixRaw lower upper f N x) (test x) := by
  have actual := congrArg (starRingEnd ℂ)
    (weighted_prefix_pairing lower upper f f' N positive ordered derivative regular measured test)
  rw [inner_conj_symm, ← integral_conj] at actual
  simpa only [inner_conj_symm] using actual

theorem position_prefix_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    inner ℂ (positionPrefix coordinate shift N)
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
        ∫ x : ℝ, inner ℂ (weightedPrefixRaw (bandLower shift) 4 (positionWeight coordinate shift) N x)
          ((burnolCompletedMellinRieszVector coordinate : BurnolL2) x) :=
  weighted_prefix_pairing_left _ _ _ _ N (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => positionWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _) _

theorem fourier_prefix_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) (N : ℕ) :
    inner ℂ (fourierPrefix coordinate shift N)
      (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
        ∫ x : ℝ, inner ℂ (weightedPrefixRaw (bandLower shift) 4 (fourierWeight coordinate shift) N x)
          (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) x) :=
  weighted_prefix_pairing_left _ _ _ _ N (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => fourierWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _) _

end
end OriginalRieszFinitePairing.CoPoisson.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
