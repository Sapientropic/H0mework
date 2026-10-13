import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Arithmetic

/-! The original positive reciprocal step removes its exact n=1 seed channel.
The remaining counting channels and the original mean generate both complete
correction pairings, with the whole-axis integrability paid by the source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.Correction

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFinitePairing.CoPoisson.Energy
open OriginalRieszFinitePairing.CoPoisson.Ward.Arithmetic

noncomputable section

def higherCountingRaw (lower upper : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (∑ n ∈ (burnolReciprocalStepChannels lower upper x).erase 1, f ((n : ℝ) / |x|)) *
    ((|x| : ℝ) : ℂ)⁻¹ - ∫ u : ℝ in Ioc lower upper, f u

theorem counting_sub_source (lower upper x : ℝ) (f : ℝ → ℂ) (nonzero : x ≠ 0) :
    weightedCountingRaw lower upper f x -
      f (|x|⁻¹) * burnolReciprocalStepSourceRaw lower upper x =
        higherCountingRaw lower upper f x := by
  classical
  have first : burnolReciprocalStepSourceRaw lower upper x =
      if (1 : ℕ) ∈ burnolReciprocalStepChannels lower upper x then ((|x| : ℝ) : ℂ)⁻¹ else 0 := by
    simpa using! burnolReciprocalStep_source_term lower upper x nonzero (1 : ℕ+)
  unfold weightedCountingRaw higherCountingRaw
  rw [first]
  by_cases active : 1 ∈ burnolReciprocalStepChannels lower upper x
  · rw [if_pos active, ← Finset.sum_erase_add _ _ active]
    simp only [Nat.cast_one, one_div]
    ring
  · rw [if_neg active, mul_zero, sub_zero, Finset.erase_eq_of_notMem active]

private theorem weighted_raw_integrable (lower upper : ℝ) (f f' : ℝ → ℂ)
    (family : ℝ → BurnolL2) (raw : ℝ × ℝ → ℂ) (ordered : lower ≤ upper)
    (familyIntegral : IntegrableOn (fun u => f' u • family u) (Ioc lower upper))
    (measured : Measurable (fun point : ℝ × ℝ => f' point.1 * raw point))
    (represents : ∀ u ∈ Icc lower upper, (family u : ℝ → ℂ) =ᵐ[volume]
      fun x => raw (u, x)) (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x)
      (f upper * raw (upper, x) - ∫ u : ℝ in Ioc lower upper, f' u * raw (u, x))) := by
  have familyRead : ∀ᵐ u ∂volume.restrict (Ioc lower upper),
      (f' u • family u : BurnolL2) =ᵐ[volume] fun x => f' u * raw (u, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
    filter_upwards [Lp.coeFn_smul (f' u) (family u), represents u
      ⟨inside.1.le, inside.2⟩] with x smulAt rawAt
    rw [smulAt]
    change f' u * family u x = _
    rw [rawAt]
  have actual := burnolL2Bochner_pairing_raw (volume.restrict (Ioc lower upper))
    (fun u => f' u • family u) familyIntegral
    (fun point : ℝ × ℝ => f' point.1 * raw point) measured familyRead test
  have headRead : (f upper • family upper : BurnolL2) =ᵐ[volume]
      fun x : ℝ => f upper * raw (upper, x) := by
    filter_upwards [Lp.coeFn_smul (f upper) (family upper),
      represents upper ⟨ordered, le_rfl⟩] with x smulAt rawAt
    rw [smulAt]
    change f upper * family upper x = _
    rw [rawAt]
  have headIntegral := (L2.integrable_inner (𝕜 := ℂ) test (f upper • family upper)).congr
    (headRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx))
  simpa only [inner_sub_right, Pi.sub_apply] using! headIntegral.sub actual.1

private theorem wave_integrable (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x) (weightedCountingRaw lower upper f x)) := by
  have rawMeasured : Measurable (fun point : ℝ × ℝ => f' point.1 *
      burnolReciprocalStepWaveRaw lower point.1 point.2) := by
    apply (measured.comp measurable_fst).mul
    unfold burnolReciprocalStepWaveRaw burnolReciprocalStepWaveReal burnolReciprocalStepChannels
    simp only [Nat.card_Ico]
    apply Complex.measurable_ofReal.comp
    apply Measurable.ite (measurable_snd (measurableSet_singleton (0 : ℝ)))
    · fun_prop
    · fun_prop
  have rawRead : ∀ u ∈ Icc lower upper,
      (burnolReciprocalStepNativeWave lower u : ℝ → ℂ) =ᵐ[volume]
        burnolReciprocalStepWaveRaw lower u := by
    intro u inside
    rw [burnolReciprocalStepNativeWave_eq lower u positive inside.1]
    exact (burnolReciprocalStepWave_memLp lower u positive inside.1).coeFn_toLp
  have actual := weighted_raw_integrable lower upper f f' (burnolReciprocalStepNativeWave lower)
    (fun point => burnolReciprocalStepWaveRaw lower point.1 point.2) ordered
    (stepWave_integrable lower upper f' positive regular) rawMeasured rawRead test
  apply actual.congr
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  exact congrArg (inner ℂ (test x))
    (weighted_count_raw lower upper x f f' positive ordered nonzero derivative regular)

private theorem source_integrable (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    Integrable (fun x : ℝ => inner ℂ (test x)
      (f (|x|⁻¹) * burnolReciprocalStepSourceRaw lower upper x)) := by
  have sourceContinuous : ContinuousOn (burnolReciprocalStepNativeSource lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitReciprocalPrimitiveL2).mono
      (fun _ inside => positive.trans_le inside.1)).sub continuousOn_const
  have familyIntegral : IntegrableOn
      (fun u => f' u • burnolReciprocalStepNativeSource lower u) (Ioc lower upper) :=
    (regular.smul sourceContinuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have rawMeasured : Measurable (fun point : ℝ × ℝ => f' point.1 *
      burnolReciprocalStepSourceRaw lower point.1 point.2) := by
    have reciprocal : Measurable (fun point : ℝ × ℝ => |point.2|⁻¹) := by fun_prop
    have condition : MeasurableSet {point : ℝ × ℝ |
        lower ≤ |point.2|⁻¹ ∧ |point.2|⁻¹ < point.1} :=
      (measurableSet_le measurable_const reciprocal).inter (measurableSet_lt reciprocal measurable_fst)
    exact (measured.comp measurable_fst).mul
      (Measurable.ite condition (by fun_prop) measurable_const)
  have rawRead : ∀ u ∈ Icc lower upper,
      (burnolReciprocalStepNativeSource lower u : ℝ → ℂ) =ᵐ[volume]
        burnolReciprocalStepSourceRaw lower u := by
    intro u inside
    rw [burnolReciprocalStepNativeSource_eq lower u positive inside.1]
    exact (burnolReciprocalStepSource_memLp lower u positive inside.1).coeFn_toLp
  have actual := weighted_raw_integrable lower upper f f' (burnolReciprocalStepNativeSource lower)
    (fun point => burnolReciprocalStepSourceRaw lower point.1 point.2) ordered
    familyIntegral rawMeasured rawRead test
  apply actual.congr
  filter_upwards with x
  exact congrArg (inner ℂ (test x))
    (burnolReciprocalStepRaw_weightedIntegral lower upper x f f' derivative regular)

/-- The original weighted correction consists of every integer channel above
one and its own mean. Both terms remain combined inside the whole-axis integral. -/
private theorem correction_higher_pairing_right (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    inner ℂ test (burnolWeightedReciprocalStepWave lower upper f f' -
      burnolWeightedReciprocalStepSource lower upper f f') =
        ∫ x : ℝ, inner ℂ (test x) (higherCountingRaw lower upper f x) := by
  rw [inner_sub_right,
    weighted_wave_arithmetic_pairing lower upper f f' positive ordered derivative regular measured,
    burnolWeightedReciprocalStepSource_pairing lower upper f f' positive ordered derivative regular measured,
    ← integral_sub (wave_integrable lower upper f f' positive ordered derivative regular measured test)
      (source_integrable lower upper f f' positive ordered derivative regular measured test)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with x nonzero
  rw [← inner_sub_right, counting_sub_source lower upper x f nonzero]

theorem correction_higher_pairing (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (derivative : ∀ u ∈ Icc lower upper, HasDerivAt f (f' u) u)
    (regular : ContinuousOn f' (Icc lower upper)) (measured : Measurable f') (test : BurnolL2) :
    inner ℂ (burnolWeightedReciprocalStepWave lower upper f f' -
      burnolWeightedReciprocalStepSource lower upper f f') test =
        ∫ x : ℝ, inner ℂ (higherCountingRaw lower upper f x) (test x) := by
  have actual := congrArg (starRingEnd ℂ)
    (correction_higher_pairing_right lower upper f f' positive ordered derivative regular measured test)
  rw [inner_conj_symm, ← integral_conj] at actual
  simpa only [inner_conj_symm] using actual

theorem position_correction_higher_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    inner ℂ (positionCorrection coordinate shift)
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      ∫ x : ℝ, inner ℂ (higherCountingRaw (bandLower shift) 4 (positionWeight coordinate shift) x)
        ((burnolCompletedMellinRieszVector coordinate : BurnolL2) x) :=
  correction_higher_pairing _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => positionWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _) _

theorem fourier_correction_higher_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    inner ℂ (fourierCorrection coordinate shift)
      (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      ∫ x : ℝ, inner ℂ (higherCountingRaw (bandLower shift) 4 (fourierWeight coordinate shift) x)
        (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) x) :=
  correction_higher_pairing _ _ _ _ (bandLower_pos shift)
    (bandLower_le_four shift nonnegative)
    (fun u inside => fourierWeight_hasDerivAt coordinate shift u
      ((bandLower_pos shift).trans_le inside.1))
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) (measurable_deriv _) _

end
end OriginalRieszFinitePairing.CoPoisson.Ward.Correction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
