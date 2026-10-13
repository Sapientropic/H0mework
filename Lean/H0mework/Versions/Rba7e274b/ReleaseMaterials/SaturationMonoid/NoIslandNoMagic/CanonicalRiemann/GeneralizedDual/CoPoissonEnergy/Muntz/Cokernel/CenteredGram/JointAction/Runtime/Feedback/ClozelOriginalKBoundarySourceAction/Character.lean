import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance boundaryCharacterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Source
export OriginalKConstantContactSourceAction.ConstantSource (value velocity seed)
end Source
local notation "P" => burnolEvenAmbientProjection


local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualBoundaryPricedSourceCharacter (h : ℝ) (_nonnegative : 0 ≤ h) (_bounded : h ≤ Real.log 2) : ℂ :=
  2 * (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) +
  2 * star (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) +
  actualFullBoundarySourcePrice observation nontrivial half h -
  2 * (observation.coordinate/2-1/4) *
    inner ℂ (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h)
      (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h) -
  2 * star (observation.coordinate/2-1/4) *
    inner ℂ (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h)
      (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h) +
  OriginalKWholeWardSource.actualWholeMixedWaveSourcePrice observation nontrivial half h +
  2 * OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h

/-- The literal independent Cross consumes the newly generated full physical boundary source integral; all whole-wave, complement and outside fees remain. -/
theorem actual_original_cross_consumes_boundary_source_action (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualBoundaryPricedSourceCharacter observation nontrivial half h nonnegative bounded := by
  have source := OriginalKWholeWardSource.actual_original_cross_whole_source_character
    observation nontrivial half h nonnegative bounded
  unfold OriginalKWholeWardSource.actualWholePricedSourceCharacter at source
  rw [actual_full_physical_boundary_source_price observation nontrivial half h nonnegative bounded] at source
  exact source

/-- The current eight-slot programme and all five original residues consume this same source boundary action. -/
theorem actual_current_character_consumes_boundary_source_action (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
      actualBoundaryPricedSourceCharacter observation nontrivial half h nonnegative bounded := by
  have source := OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action
    observation nontrivial half h nonnegative bounded n
  rw [actual_original_cross_consumes_boundary_source_action observation nontrivial half h nonnegative bounded] at source
  exact source.symm

theorem actual_boundary_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    Tendsto (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded)
      atTop (𝓝 (actualBoundaryPricedSourceCharacter observation nontrivial half h nonnegative bounded)) := by
  have source := OriginalKWaveSourceAction.actual_original_band_source_character_closure
    observation nontrivial half h nonnegative bounded
  rw [actual_original_cross_consumes_boundary_source_action observation nontrivial half h nonnegative bounded] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
