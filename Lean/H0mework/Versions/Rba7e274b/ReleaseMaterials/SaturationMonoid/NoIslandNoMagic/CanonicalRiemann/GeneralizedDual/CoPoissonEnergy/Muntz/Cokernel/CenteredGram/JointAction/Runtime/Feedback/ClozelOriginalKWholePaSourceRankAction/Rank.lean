import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Effect
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaRankComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

def actualWholePaDivisionCoordinate : BurnolCompletedMellinCoordinate :=
  burnolDivisionZeroCompletedMellinCoordinate observation (c).rightHalf

def actualWholePaSourceCoefficient (h : ℝ) : ℂ :=
  burnolPaResolventSourceCoefficient (actualWholePaDivisionCoordinate observation nontrivial half)
    (actualWholePaSource observation nontrivial half h)

def actualOriginalUnitPaTail : BurnolPaAmbientCarrier :=
  OP (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf)
def actualOriginalUnitPaPair : BurnolPaAmbientCarrier :=
  (burnolZeroOwnedUnitFourierPaState observation nontrivial (c).rightHalf : BurnolPaAmbientCarrier)
def actualOriginalUnitPaSibling : BurnolPaAmbientCarrier :=
  (2 : ℂ) • actualOriginalUnitPaTail observation nontrivial half - actualOriginalUnitPaPair observation nontrivial half

/-- The complete actual Pa source uses the original full unit tail rank, retaining its own coefficient. -/
theorem actual_whole_Pa_R_source_rank (h : ℝ) :
    Q (actualWholePaR observation nontrivial half h) =
      actualWholePaSourceCoefficient observation nontrivial half h • actualOriginalUnitPaTail observation nontrivial half := by
  let source := actualWholePaSource observation nontrivial half h
  have member := actual_whole_Pa_source_qualified observation nontrivial half h
  have generated := burnolPaResolventPhysicalResponse_Q observation nontrivial (c).rightHalf source member
  have realized : P (actualWholePaR observation nontrivial half h) =
      burnolPaResolventPhysicalResponse observation nontrivial (c).rightHalf source member := by
    have physical := actual_whole_Pa_R_physical observation nontrivial half h
    let value : BurnolPaAmbientCarrier := ⟨actualWholePaR observation nontrivial half h,physical⟩
    have own := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
    change P (actualWholePaR observation nontrivial half h) = value at own
    rw [own]
    rfl
  change OP (P (actualWholePaR observation nontrivial half h)) = _
  rw [realized]
  exact generated

/-- The original paired source rank is paid after the same full Pa R action. -/
theorem actual_whole_Pa_paired_source_rank (h : ℝ) :
    Q (actualWholePaPairedR observation nontrivial half h) =
      (actualWholePaSourceCoefficient observation nontrivial half h / 2) •
        actualOriginalUnitPaPair observation nontrivial half := by
  let source := actualWholePaSource observation nontrivial half h
  have member := actual_whole_Pa_source_qualified observation nontrivial half h
  let response := burnolPaResolventPhysicalResponse observation nontrivial (c).rightHalf source member
  have generated := burnolPaResolventPhysicalResponse_pairedQ observation nontrivial (c).rightHalf source member
  have realized : P (actualWholePaPairedR observation nontrivial half h) =
      (1/2 : ℂ) • (response + Fphysical response) := by
    have physical := (actual_whole_Pa_four_faces_physical observation nontrivial half h).1
    let value : BurnolPaAmbientCarrier := ⟨actualWholePaPairedR observation nontrivial half h,physical⟩
    have own := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
    change P (actualWholePaPairedR observation nontrivial half h) = value at own
    rw [own]
    apply Subtype.ext
    rfl
  change OP (P (actualWholePaPairedR observation nontrivial half h)) = _
  rw [realized]
  exact generated

/-- The sibling's original unit rank follows from this same R/paired source inventory; it is never erased. -/
theorem actual_whole_Pa_sibling_source_rank (h : ℝ) :
    Q (actualWholePaSiblingR observation nontrivial half h) =
      (actualWholePaSourceCoefficient observation nontrivial half h / 2) •
        actualOriginalUnitPaSibling observation nontrivial half := by
  have split : actualWholePaSiblingR observation nontrivial half h =
      actualWholePaR observation nontrivial half h - actualWholePaPairedR observation nontrivial half h := by
    unfold actualWholePaSiblingR actualWholePaPairedR OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
    module
  rw [split,map_sub,actual_whole_Pa_R_source_rank,actual_whole_Pa_paired_source_rank]
  unfold actualOriginalUnitPaSibling
  module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
