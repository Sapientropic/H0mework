import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWaveDivisionAction.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWaveDivisionAction.Price
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wavePhysicalCharacterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


def actualWavePhysicalPricedSourceCharacter (h : ℝ) (_nonnegative : 0 ≤ h) (_bounded : h ≤ Real.log 2) : ℂ :=
  2 * (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) +
  2 * star (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) +
  OriginalKPhysicalWindowSourceAction.actualPhysicalWindowFullBoundaryPrice observation nontrivial half h -
  2 * (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h))
      (P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h)) -
  2 * star (observation.coordinate/2-1/4) *
    inner ℂ (P (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h))
      (P (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h)) +
  OriginalKWholeWardSource.actualWholeMixedWaveSourcePrice observation nontrivial half h +
  2 * actualComplementOutsideFlux observation nontrivial half h



/-- The actual generated physical wave qualifications pay its projected Gram and erase its Outside legs in the literal original Cross consumer. -/
theorem actual_original_cross_consumes_physical_wave_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualWavePhysicalPricedSourceCharacter observation nontrivial half h nonnegative bounded := by
  have source := OriginalKPhysicalWindowSourceAction.actual_original_cross_consumes_physical_window_action
    observation nontrivial half h nonnegative bounded
  have gram := actual_physical_wave_gram observation nontrivial half h nonnegative bounded
  have outside := actual_outside_flux_consumes_physical_wave observation nontrivial half h nonnegative bounded
  unfold OriginalKPhysicalWindowSourceAction.actualPhysicalWindowPricedSourceCharacter at source
  rw [← gram.1,← gram.2,outside] at source
  exact source

theorem actual_current_character_consumes_physical_wave_source (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
      actualWavePhysicalPricedSourceCharacter observation nontrivial half h nonnegative bounded := by
  have source := OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action
    observation nontrivial half h nonnegative bounded n
  rw [actual_original_cross_consumes_physical_wave_source observation nontrivial half h nonnegative bounded] at source
  exact source.symm

theorem actual_physical_wave_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    Tendsto (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded)
      atTop (𝓝 (actualWavePhysicalPricedSourceCharacter observation nontrivial half h nonnegative bounded)) := by
  have source := OriginalKWaveSourceAction.actual_original_band_source_character_closure observation nontrivial half h nonnegative bounded
  rw [actual_original_cross_consumes_physical_wave_source observation nontrivial half h nonnegative bounded] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
