import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeWardSource.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
open Complex MeasureTheory BurnolPhysicalState Filter
open scoped Topology
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholeCharacterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualWholePricedSourceCharacter (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : ℂ :=
  2 * (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) +
  2 * star (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) +
  actualWholePhysicalBoundaryCross observation nontrivial half h nonnegative bounded -
  2 * (observation.coordinate/2-1/4) *
    inner ℂ (actualWholeWavePairedR observation nontrivial half h)
      (actualWholeWavePairedR observation nontrivial half h) -
  2 * star (observation.coordinate/2-1/4) *
    inner ℂ (actualWholeWaveSiblingR observation nontrivial half h)
      (actualWholeWaveSiblingR observation nontrivial half h) +
  actualWholeMixedWaveSourcePrice observation nontrivial half h +
  2 * OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h

/-- The original independent Cross consumer takes the generated whole physical Ward and paid whole-wave diagonal, retaining full boundary, mixed Pa and outside fees. -/
theorem actual_original_cross_whole_source_character (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualWholePricedSourceCharacter observation nontrivial half h nonnegative bounded := by
  have source := actual_whole_physical_source_Ward observation nontrivial half h nonnegative bounded
  rw [actual_physical_kernel_cross_original,
    actual_whole_wave_quadratic_cotest_price observation nontrivial half h nonnegative bounded] at source
  unfold actualWholePricedSourceCharacter
  linear_combination -2 * source

/-- The current literal eight-slot band programme and all five original residues consume the new source-priced whole Ward equation. -/
theorem actual_current_character_consumes_whole_source_Ward (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
    actualWholePricedSourceCharacter observation nontrivial half h nonnegative bounded := by
  have current := OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action
    observation nontrivial half h nonnegative bounded n
  rw [actual_original_cross_whole_source_character observation nontrivial half h nonnegative bounded] at current
  exact current.symm

/-- The existing literal band closure reads the complete source-generated Ward price. -/
theorem actual_whole_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    Tendsto (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded)
      atTop (𝓝 (actualWholePricedSourceCharacter observation nontrivial half h nonnegative bounded)) := by
  have source := OriginalKWaveSourceAction.actual_original_band_source_character_closure
    observation nontrivial half h nonnegative bounded
  rw [actual_original_cross_whole_source_character observation nontrivial half h nonnegative bounded] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
