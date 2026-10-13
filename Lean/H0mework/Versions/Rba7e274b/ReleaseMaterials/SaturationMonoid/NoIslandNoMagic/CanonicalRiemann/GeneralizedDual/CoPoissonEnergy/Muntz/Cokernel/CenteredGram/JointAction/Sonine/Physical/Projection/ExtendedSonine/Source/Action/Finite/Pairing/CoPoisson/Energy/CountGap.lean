import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.ZeroRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson

noncomputable section

theorem step_correction_half_raw (lower upper x : ℝ) (positive : 0 < lower) (ordered : lower ≤ upper)
    (bounded : upper ≤ 4) (small : |x| ≤ 1 / 2) :
    burnolReciprocalStepWaveRaw lower upper x - burnolReciprocalStepSourceRaw lower upper x =
      ((lower - upper : ℝ) : ℂ) := by
  have forward : burnolInnerGapForward (burnolReciprocalStepSourceRaw lower upper) x =
      burnolReciprocalStepSourceRaw lower upper x := by
    unfold burnolInnerGapForward
    rw [tsum_eq_single (1 : ℕ+)]
    · norm_num
    · intro n different
      have natDifferent : (n : ℕ) ≠ 1 := fun equal => different (Subtype.ext equal)
      have two : 2 ≤ (n : ℕ) := by have := n.pos; omega
      have denominator : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
      have castTwo : (2 : ℝ) ≤ (n : ℕ) := by exact_mod_cast two
      have smallScaled : |x / (n : ℕ)| ≤ upper⁻¹ := by
        apply le_trans _ ((inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) (positive.trans_le ordered)).mpr bounded)
        rw [abs_div, abs_of_pos denominator]
        apply (div_le_iff₀ denominator).mpr
        norm_num
        nlinarith
      rw [burnolReciprocalStepSource_innerGap lower upper positive ordered smallScaled, mul_zero]
  rw [burnolReciprocalStepWave_coSum lower upper x positive, forward]
  push_cast
  ring

theorem half_inner_zero_of_local_constant (value test : BurnolL2) (coefficient : ℂ)
    (constant : ∀ᵐ x ∂volume, x ∈ symmetricInterval (1 / 2 : ℝ) → value x = coefficient)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test value = 0 := by
  have density : (fun x : ℝ => inner ℂ (test x) (value x)) =ᵐ[volume]
      fun x => star (test x) * coefficient := by
    filter_upwards [constant, originalPhysicalCutoff_coeFn (1 / 2) test] with x actual cutoff
    rw [supported] at cutoff
    by_cases inside : x ∈ symmetricInterval (1 / 2 : ℝ)
    · rw [actual inside]
      simp only [RCLike.inner_apply, starRingEnd_apply]
      ring
    · rw [indicator_of_notMem inside] at cutoff
      rw [cutoff]
      simp
  rw [L2.inner_def, integral_congr_ae density, integral_mul_const]
  change (∫ x : ℝ, starRingEnd ℂ (test x)) * coefficient = 0
  rw [integral_conj, mass]
  simp

theorem step_wave_source_half_inner (lower upper : ℝ) (positive : 0 < lower) (ordered : lower ≤ upper)
    (bounded : upper ≤ 4) (test : BurnolL2) (supported : originalPhysicalCutoff (1 / 2) test = test)
    (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (burnolReciprocalStepNativeWave lower upper) =
      inner ℂ test (burnolReciprocalStepNativeSource lower upper) := by
  have raw : ∀ᵐ x ∂volume, x ∈ symmetricInterval (1 / 2 : ℝ) →
      (burnolReciprocalStepNativeWave lower upper - burnolReciprocalStepNativeSource lower upper : BurnolL2) x =
        ((lower - upper : ℝ) : ℂ) := by
    rw [burnolReciprocalStepNativeWave_eq lower upper positive ordered,
      burnolReciprocalStepNativeSource_eq lower upper positive ordered]
    filter_upwards [Lp.coeFn_sub (burnolReciprocalStepWaveL2 lower upper positive ordered)
      (burnolReciprocalStepSourceL2 lower upper positive ordered),
      (burnolReciprocalStepWave_memLp lower upper positive ordered).coeFn_toLp,
      (burnolReciprocalStepSource_memLp lower upper positive ordered).coeFn_toLp]
      with x difference wave source inside
    rw [difference]
    change burnolReciprocalStepWaveL2 lower upper positive ordered x -
      burnolReciprocalStepSourceL2 lower upper positive ordered x = _
    unfold burnolReciprocalStepWaveL2 burnolReciprocalStepSourceL2
    rw [wave, source]
    exact step_correction_half_raw lower upper x positive ordered bounded (abs_le.mpr inside)
  have paired := half_inner_zero_of_local_constant _ test _ raw supported mass
  rwa [inner_sub_right, sub_eq_zero] at paired

theorem stepWave_integrable (lower upper : ℝ) (f' : ℝ → ℂ) (positive : 0 < lower)
    (regular : ContinuousOn f' (Icc lower upper)) :
    IntegrableOn (fun u => f' u • burnolReciprocalStepNativeWave lower u) (Ioc lower upper) := by
  have continuous : ContinuousOn (burnolReciprocalStepNativeWave lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitCountingPrimitiveL2).mono
      (fun _ inside => positive.trans_le inside.1)).sub continuousOn_const
  exact (regular.smul continuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem weighted_wave_read (lower upper : ℝ) (f f' : ℝ → ℂ) (positive : 0 < lower)
    (regular : ContinuousOn f' (Icc lower upper)) (read : BurnolL2 →L[ℂ] ℂ) :
    read (burnolWeightedReciprocalStepWave lower upper f f') =
      f upper * read (burnolReciprocalStepNativeWave lower upper) -
        ∫ u : ℝ in Ioc lower upper, f' u * read (burnolReciprocalStepNativeWave lower u) := by
  rw [burnolWeightedReciprocalStepWave, map_sub, map_smul,
    ← read.integral_comp_comm (stepWave_integrable lower upper f' positive regular)]
  simp only [map_smul, smul_eq_mul]

private theorem weighted_source_read (lower upper : ℝ) (f f' : ℝ → ℂ) (positive : 0 < lower)
    (regular : ContinuousOn f' (Icc lower upper)) (read : BurnolL2 →L[ℂ] ℂ) :
    read (burnolWeightedReciprocalStepSource lower upper f f') =
      f upper * read (burnolReciprocalStepNativeSource lower upper) -
        ∫ u : ℝ in Ioc lower upper, f' u * read (burnolReciprocalStepNativeSource lower u) := by
  have continuous : ContinuousOn (burnolReciprocalStepNativeSource lower) (Icc lower upper) :=
    ((burnolSourceScalePrimitive_continuous burnolUnitReciprocalPrimitiveL2).mono
      (fun _ inside => positive.trans_le inside.1)).sub continuousOn_const
  have integrable : IntegrableOn (fun u => f' u • burnolReciprocalStepNativeSource lower u)
      (Ioc lower upper) := (regular.smul continuous).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [burnolWeightedReciprocalStepSource, map_sub, map_smul, ← read.integral_comp_comm integrable]
  simp only [map_smul, smul_eq_mul]

theorem weighted_wave_source_half_inner (lower upper : ℝ) (f f' : ℝ → ℂ)
    (positive : 0 < lower) (ordered : lower ≤ upper) (bounded : upper ≤ 4)
    (regular : ContinuousOn f' (Icc lower upper)) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (burnolWeightedReciprocalStepWave lower upper f f') =
      inner ℂ test (burnolWeightedReciprocalStepSource lower upper f f') := by
  have wave := weighted_wave_read lower upper f f' positive regular (innerSL ℂ test)
  have source := weighted_source_read lower upper f f' positive regular (innerSL ℂ test)
  change inner ℂ test (burnolWeightedReciprocalStepWave lower upper f f') = _ at wave
  change inner ℂ test (burnolWeightedReciprocalStepSource lower upper f f') = _ at source
  rw [wave, source]
  change f upper * inner ℂ test (burnolReciprocalStepNativeWave lower upper) - _ =
    f upper * inner ℂ test (burnolReciprocalStepNativeSource lower upper) - _
  rw [step_wave_source_half_inner lower upper positive ordered bounded test supported mass]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u inside
  exact congrArg (fun z : ℂ => f' u * z)
    (step_wave_source_half_inner lower u positive inside.1.le (inside.2.trans bounded) test supported mass)

theorem positionWave_half_inner (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (positionWave coordinate shift) = inner ℂ test (positionSeed coordinate shift) :=
  weighted_wave_source_half_inner _ _ _ _ (bandLower_pos shift) (bandLower_le_four shift nonnegative) le_rfl
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) test supported mass

theorem fourierWave_half_inner (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (fourierWave coordinate shift) = inner ℂ test (fourierSeed coordinate shift) :=
  weighted_wave_source_half_inner _ _ _ _ (bandLower_pos shift) (bandLower_le_four shift nonnegative) le_rfl
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) test supported mass

end
end OriginalRieszFinitePairing.CoPoisson.Energy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
