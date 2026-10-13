import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Effect
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
local instance waveCharacterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "K" => burnolCompletedMellinRieszVector
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q

def actualBandFiniteWaveResponse (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (n : Nat) : BurnolPaAmbientCarrier :=
  actualBandCoefficientAction coordinate h • Q
    (OriginalKPaCountingSourceAction.actualFiniteCountingUnitSource coordinate
      (OriginalKPaCountingSourceAction.actualCountingCutoff n))
def actualBandWaveResponseResidual (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (n : Nat) : BurnolPaAmbientCarrier :=
  actualBandCoefficientAction coordinate h • Q
    (OriginalKPaCountingSourceAction.actualCountingOriginResidual coordinate
      (OriginalKPaCountingSourceAction.actualCountingCutoff n))

theorem actual_original_wave_full_counting_action (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (n : Nat) :
    Q (burnolDirectRightResolvent (coordinate.value / 2)
      (OriginalCommonInverseForcing.SourceJoint.upperSourceWave coordinate h)) -
      actualBandFiniteWaveResponse coordinate h n = actualBandWaveResponseResidual coordinate h n := by
  have source := OriginalKPaCountingSourceAction.actual_original_Pa_counting_response_residual coordinate
    (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient coordinate h nonnegative bounded)
    (OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa coordinate h nonnegative bounded) n
  unfold OriginalKPaCountingSourceAction.actualFinitePaCountingResponse
    OriginalKPaCountingSourceAction.actualPaCountingResponseResidual at source
  rw [actual_original_upper_wave_band_action] at source
  exact source

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualBandFiniteWavePairPrice (h : ℝ) (n : Nat) : ℂ :=
  star (inner ℂ (K c + Fphysical (K c)) (actualBandFiniteWaveResponse c h n))
def actualBandFiniteWaveSiblingPrice (h : ℝ) (n : Nat) : ℂ :=
  inner ℂ (K c - Fphysical (K c)) (actualBandFiniteWaveResponse c h n)

theorem actual_current_wave_prices_consume_source_action (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKPaCountingSourceAction.actualFiniteWavePairPrice observation nontrivial half h nonnegative bounded n =
      actualBandFiniteWavePairPrice observation nontrivial half h n ∧
    OriginalKPaCountingSourceAction.actualFiniteWaveSiblingPrice observation nontrivial half h nonnegative bounded n =
      actualBandFiniteWaveSiblingPrice observation nontrivial half h n := by
  unfold OriginalKPaCountingSourceAction.actualFiniteWavePairPrice
    OriginalKPaCountingSourceAction.actualFiniteWaveSiblingPrice
    OriginalKPaCountingSourceAction.actualFinitePaCountingResponse OriginalKPaCountingSourceAction.actualWaveSource
  rw [actual_original_upper_wave_band_action]
  exact ⟨rfl, rfl⟩

def actualBandSourceFiniteCharacter (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (n : Nat) : ℂ :=
  (OriginalKSourceScaledMaximalResponse.Return.sourceA observation)⁻¹ *
    OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterRead observation nontrivial half h nonnegative bounded
      (OriginalKRealCoordinateSourceUnit.actualUnweightedFiniteKPrice c h n)
      (OriginalKRealCoordinateSourceUnit.actualUnweightedFiniteFKPrice c h n)
      (OriginalKFourierForcingCofinalAction.actualFiniteFourierForcingPrice c h n)
      (OriginalKPrimitivePhysicalSourceAction.actualFiniteKForcingPrice observation nontrivial half h n)
      (OriginalKRealCoordinateSourceUnit.actualUnweightedPrimitivePairPrice observation nontrivial half h n)
      (OriginalKRealCoordinateSourceUnit.actualUnweightedPrimitiveSiblingPrice observation nontrivial half h n)
      (actualBandFiniteWavePairPrice observation nontrivial half h n)
      (actualBandFiniteWaveSiblingPrice observation nontrivial half h n)

/-- The literal current eight-slot character BODY consumes both generated wave actions while preserving all original M, primitive, forcing, and source error inventories. -/
theorem actual_current_character_consumes_original_wave_action (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKRealCoordinateSourceUnit.actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded n =
      actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n := by
  unfold OriginalKRealCoordinateSourceUnit.actualUnweightedFiniteCharacter actualBandSourceFiniteCharacter
  have source := actual_current_wave_prices_consume_source_action observation nontrivial half h nonnegative bounded n
  rw [source.1, source.2]

theorem actual_original_cross_consumes_generated_wave_action (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
        OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n := by
  have source := OriginalKRealCoordinateSourceUnit.actual_original_unweighted_character observation nontrivial half h nonnegative bounded n
  rw [actual_current_character_consumes_original_wave_action] at source
  exact source

theorem actual_original_band_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    Tendsto (actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded) atTop
      (𝓝 (OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)) := by
  have source := OriginalKRealCoordinateSourceUnit.actual_original_unweighted_character_tendsto observation nontrivial half h nonnegative bounded
  have actual : OriginalKRealCoordinateSourceUnit.actualUnweightedFiniteCharacter observation nontrivial half h nonnegative bounded =
      actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded := by
    funext n
    exact actual_current_character_consumes_original_wave_action observation nontrivial half h nonnegative bounded n
  rw [actual] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
