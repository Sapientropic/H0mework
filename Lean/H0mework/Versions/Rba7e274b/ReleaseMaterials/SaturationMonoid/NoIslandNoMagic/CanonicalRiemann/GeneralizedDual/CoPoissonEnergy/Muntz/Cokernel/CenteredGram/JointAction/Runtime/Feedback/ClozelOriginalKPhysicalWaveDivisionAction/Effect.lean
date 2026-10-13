import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWaveDivisionAction.Division
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
local instance waveOutsideEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "O" => OriginalKPairedResponseGramAction.originalOutside

def actualComplementPairedVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • OriginalKWholeWardSource.actualWholeComplementSiblingR observation nontrivial half h +
    (1/2 : ℂ) • (actualComplementMaterial observation nontrivial half h -
      fourierL2 (actualComplementMaterial observation nontrivial half h))
def actualComplementSiblingVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • OriginalKWholeWardSource.actualWholeComplementPairedR observation nontrivial half h +
    (1/2 : ℂ) • (actualComplementMaterial observation nontrivial half h +
      fourierL2 (actualComplementMaterial observation nontrivial half h))

/-- The complete same complement has its own source-generated R action before any Outside price is formed. -/
theorem actual_complement_R_source_action (h : ℝ) :
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
      (OriginalKWholeWardSource.actualWholeComplementPairedR observation nontrivial half h))
      (actualComplementPairedVelocity observation nontrivial half h) 0 ∧
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
      (OriginalKWholeWardSource.actualWholeComplementSiblingR observation nontrivial half h))
      (actualComplementSiblingVelocity observation nontrivial half h) 0 := by
  have source := OriginalKFullSourceRResponse.Paid.ambient_R_paired_equations _
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)
    (actualComplementMaterial observation nontrivial half h)
  simpa only [OriginalKWholeWardSource.actualWholeComplementPairedR,
    OriginalKWholeWardSource.actualWholeComplementSiblingR, OriginalKWholeWardSource.actualWholeComplementR,
    actual_complement_material_realizes, OriginalKCombCofinalRAction.original_R_direct,
    actualComplementPairedVelocity,actualComplementSiblingVelocity] using source

/-- The paid same-source physical qualifications remove every born-wave Outside leg. -/
theorem actual_whole_wave_outside_zero (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    O (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h) = 0 ∧
    O (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h) = 0 ∧
    O (OriginalKWholeWardSource.actualWholeWavePairedVelocity observation nontrivial half h) = 0 ∧
    O (OriginalKWholeWardSource.actualWholeWaveSiblingVelocity observation nontrivial half h) = 0 := by
  have source := actual_whole_wave_four_faces_physical observation nontrivial half h nonnegative bounded
  exact ⟨Submodule.starProjection_orthogonal_apply_eq_zero source.1,
    Submodule.starProjection_orthogonal_apply_eq_zero source.2.1,
    Submodule.starProjection_orthogonal_apply_eq_zero source.2.2.1,
    Submodule.starProjection_orthogonal_apply_eq_zero source.2.2.2⟩

private theorem actual_whole_complement_velocity_split (h : ℝ) :
    OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h =
      OriginalKWholeWardSource.actualWholeWavePairedVelocity observation nontrivial half h +
      actualComplementPairedVelocity observation nontrivial half h ∧
    OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h =
      OriginalKWholeWardSource.actualWholeWaveSiblingVelocity observation nontrivial half h +
      actualComplementSiblingVelocity observation nontrivial half h := by
  have response := OriginalKWholeWardSource.actual_whole_response_wave_complement observation nontrivial half h
  have material : OriginalKFullSourceRResponse.completeSource observation nontrivial half h =
      OriginalKWholeWardSource.actualWholeWaveSource observation nontrivial half h +
      actualComplementMaterial observation nontrivial half h := by
    have source := actual_complement_material_realizes observation nontrivial half h
    unfold OriginalKWholeWardSource.actualWholeSourceComplement at source
    linear_combination (norm := module) source
  unfold OriginalKPairedResponseGramAction.pairedVelocity OriginalKPairedResponseGramAction.siblingVelocity
    OriginalKWholeWardSource.actualWholeWavePairedVelocity OriginalKWholeWardSource.actualWholeWaveSiblingVelocity
    actualComplementPairedVelocity actualComplementSiblingVelocity
  rw [response.1,response.2,material,map_add]
  constructor <;> module

def actualComplementOutsideFlux (h : ℝ) : ℂ :=
  inner ℂ (O (OriginalKWholeWardSource.actualWholeComplementPairedR observation nontrivial half h))
    (O (actualComplementSiblingVelocity observation nontrivial half h)) +
  inner ℂ (O (actualComplementPairedVelocity observation nontrivial half h))
    (O (OriginalKWholeWardSource.actualWholeComplementSiblingR observation nontrivial half h))

/-- The literal complete OutsideFlux consumer loses its paid wave legs and keeps the whole actual complement source action. -/
theorem actual_outside_flux_consumes_physical_wave (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h =
      actualComplementOutsideFlux observation nontrivial half h := by
  have response := OriginalKWholeWardSource.actual_whole_response_wave_complement observation nontrivial half h
  have velocity := actual_whole_complement_velocity_split observation nontrivial half h
  have wave := actual_whole_wave_outside_zero observation nontrivial half h nonnegative bounded
  unfold OriginalKPairedResponseGramAction.actualOutsideFlux actualComplementOutsideFlux
  rw [response.1,response.2,velocity.1,velocity.2]
  simp only [map_add,wave.1,wave.2.1,wave.2.2.1,wave.2.2.2,zero_add]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
