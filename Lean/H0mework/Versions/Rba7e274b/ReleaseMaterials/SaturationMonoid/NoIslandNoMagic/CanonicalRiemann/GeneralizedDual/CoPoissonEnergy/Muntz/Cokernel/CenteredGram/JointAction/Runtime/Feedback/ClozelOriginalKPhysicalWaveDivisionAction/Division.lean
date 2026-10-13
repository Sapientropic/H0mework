import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWaveDivisionAction.Source
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
local instance wavePhysicalSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


/-- Actual born Pa source consumes the existing original rho/2 Division producer; this pays its full physical R qualification. -/
theorem actual_whole_wave_R_physical (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKWholeWardSource.actualWholeWaveR observation nontrivial half h ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let wave := OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded
  have sourceIn := OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h nonnegative bounded
  have rightHalf : 1/2 < observation.coordinate.re := by
    have source := (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
    exact source
  have paid := burnolPaResolvent_physical observation nontrivial rightHalf wave sourceIn
  simpa only [OriginalKWholeWardSource.actualWholeWaveR, OriginalKWholeWardSource.actualWholeWaveSource,
    OriginalKCombCofinalRAction.original_R_direct, wave,
    OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient] using paid

/-- Fourier and both dependent R faces belong to this same paid physical wave response. -/
theorem actual_whole_wave_four_faces_physical (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
    OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
    OriginalKWholeWardSource.actualWholeWavePairedVelocity observation nontrivial half h ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
    OriginalKWholeWardSource.actualWholeWaveSiblingVelocity observation nontrivial half h ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let face := evenBurnolClosedFace burnolUnscaledCommonGapRadius
  have r := actual_whole_wave_R_physical observation nontrivial half h nonnegative bounded
  have fr : fourierL2 (OriginalKWholeWardSource.actualWholeWaveR observation nontrivial half h) ∈ face := by
    exact fourierL2_mem_evenBurnolClosedFace r
  have wave : OriginalKWholeWardSource.actualWholeWaveSource observation nontrivial half h ∈ face :=
    (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded).property
  have fwave : fourierL2 (OriginalKWholeWardSource.actualWholeWaveSource observation nontrivial half h) ∈ face :=
    fourierL2_mem_evenBurnolClosedFace wave
  have pair : OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h ∈ face :=
    face.smul_mem _ (face.add_mem r fr)
  have sibling : OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h ∈ face :=
    face.smul_mem _ (face.sub_mem r fr)
  exact ⟨pair,sibling,
    face.add_mem (face.smul_mem _ sibling) (face.smul_mem _ (face.sub_mem wave fwave)),
    face.add_mem (face.smul_mem _ pair) (face.smul_mem _ (face.add_mem wave fwave))⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
