import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFinitePairing OriginalPaPhysicalGreen
local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

def actualWaveCoefficientProgramme (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  (2 : ℂ) * burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
    (burnolTateReciprocalL2 (actualUpperWaveWindowSource coordinate h))

theorem actual_original_wave_programme_identity (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    actualWaveCoefficientProgramme coordinate h = actualBandCoefficientAction coordinate h := by
  have source := actual_original_upper_wave_complete_source coordinate h nonnegative bounded
  have effect := actual_original_upper_wave_band_action coordinate h nonnegative bounded
  change (2 : ℂ) * burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 _)) = _ at effect
  rw [source] at effect
  exact effect

/-- The actual finite actor's original coefficient has the source-generated initial action; the closed band programme is not substituted by a same-valued receiver. -/
theorem actual_original_wave_coefficient_action_at_origin (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivWithinAt (actualWaveCoefficientProgramme coordinate)
      ((q : ℂ) * actualPositionBandDensity coordinate q +
        (q : ℂ) * actualFourierBandDensity coordinate q) (Icc 0 (Real.log 2)) 0 := by
  have source := (actual_original_wave_band_action_first coordinate).hasDerivWithinAt (s := Icc 0 (Real.log 2))
  apply source.congr
  · intro h admitted
    exact actual_original_wave_programme_identity coordinate h admitted.1 admitted.2
  · exact actual_original_wave_programme_identity coordinate 0 le_rfl
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

theorem actual_original_cross_wave_band_feet (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
      (OriginalKPairedResponseGramAction.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded) =
      star (actualBandCoefficientAction c h *
        (inner ℂ (K c : BurnolL2) (burnolUnitTailResponse c 4) +
          inner ℂ (fourierL2 (K c : BurnolL2)) (burnolUnitTailResponse c 4))) ∧
    OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
      (OriginalKPairedResponseGramAction.actualOriginalWaveRStock observation nontrivial half h nonnegative bounded) =
      actualBandCoefficientAction c h *
        (inner ℂ (K c : BurnolL2) (burnolUnitTailResponse c 4) -
          inner ℂ (fourierL2 (K c : BurnolL2)) (burnolUnitTailResponse c 4)) := by
  have source := actual_original_upper_wave_band_action c h nonnegative bounded
  change burnolPaResolventSourceCoefficient c
    (OriginalKPairedResponseGramAction.actualOriginalWaveStock observation nontrivial half h nonnegative bounded) = _ at source
  constructor
  · rw [OriginalKPairedResponseGramAction.actual_original_wave_pair_price, source]
  · rw [OriginalKPairedResponseGramAction.actual_original_wave_sibling_price, source]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
