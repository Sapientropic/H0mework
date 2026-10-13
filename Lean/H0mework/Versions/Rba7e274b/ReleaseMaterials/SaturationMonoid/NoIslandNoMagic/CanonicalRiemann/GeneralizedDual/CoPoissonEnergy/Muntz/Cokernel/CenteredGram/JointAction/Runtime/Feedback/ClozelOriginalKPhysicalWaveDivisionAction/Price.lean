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
local instance wavePhysicalPriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


def actualPhysicalWavePairedR (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : BurnolPaAmbientCarrier :=
  ⟨OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h,
    (actual_whole_wave_four_faces_physical observation nontrivial half h nonnegative bounded).1⟩
def actualPhysicalWaveSiblingR (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) : BurnolPaAmbientCarrier :=
  ⟨OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h,
    (actual_whole_wave_four_faces_physical observation nontrivial half h nonnegative bounded).2.1⟩

/-- The physical wave Gram is paid by the generated exact R qualification, never a pre-projection norm assumption. -/
theorem actual_physical_wave_gram (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h))
      (P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h)) =
      inner ℂ (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h)
        (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h) ∧
    inner ℂ (P (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h))
      (P (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h)) =
      inner ℂ (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h)
        (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h) := by
  have pair : P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h) =
      actualPhysicalWavePairedR observation nontrivial half h nonnegative bounded :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (actualPhysicalWavePairedR observation nontrivial half h nonnegative bounded)
  have sibling : P (OriginalKWholeWardSource.actualWholeWaveSiblingR observation nontrivial half h) =
      actualPhysicalWaveSiblingR observation nontrivial half h nonnegative bounded :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (actualPhysicalWaveSiblingR observation nontrivial half h nonnegative bounded)
  exact ⟨by rw [pair]; rfl, by rw [sibling]; rfl⟩

/-- The born Pa wave's Q rank is the original source coefficient and original unit tail, not zero by membership or value coincidence. -/
theorem actual_wave_R_source_Q_rank (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    type_of% (burnolPaResolventPhysicalResponse_Q observation nontrivial
      (show 1/2 < observation.coordinate.re from (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)
      (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded)
      (OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h nonnegative bounded)) :=
  burnolPaResolventPhysicalResponse_Q observation nontrivial
    (show 1/2 < observation.coordinate.re from (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)
    (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded)
    (OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h nonnegative bounded)


/-- The original paired wave's Pa-orthogonal rank consumes its own actual source coefficient without erasure. -/
theorem actual_wave_paired_Q_source_rank (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h)) =
    (burnolPaResolventSourceCoefficient
      (burnolDivisionZeroCompletedMellinCoordinate observation
        (show 1/2 < observation.coordinate.re from (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf))
      (OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded) / 2) •
      (burnolZeroOwnedUnitFourierPaState observation nontrivial
        (show 1/2 < observation.coordinate.re from (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf) : BurnolPaAmbientCarrier) := by
  let rightHalf : 1/2 < observation.coordinate.re := (c).rightHalf
  let wave := OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient c h nonnegative bounded
  have inPa := OriginalCommonInverseForcing.SourceJoint.actual_upper_ambient_inPa c h nonnegative bounded
  let response := burnolPaResolventPhysicalResponse observation nontrivial rightHalf wave inPa
  have paid := burnolPaResolventPhysicalResponse_pairedQ observation nontrivial rightHalf wave inPa
  have physical : P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h) =
      (1/2 : ℂ) • (response + evenFaceFourierEquiv burnolUnscaledCommonGapRadius response) := by
    have generated := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (actualPhysicalWavePairedR observation nontrivial half h nonnegative bounded)
    change P (OriginalKWholeWardSource.actualWholeWavePairedR observation nontrivial half h) =
      actualPhysicalWavePairedR observation nontrivial half h nonnegative bounded at generated
    rw [generated]
    apply Subtype.ext
    rfl
  rw [physical]
  exact paid

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
