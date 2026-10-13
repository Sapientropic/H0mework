import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Source
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
local instance wholePaInventoryComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "O" => OriginalKPairedResponseGramAction.originalOutside

/-- The remaining original source is the complete same-event Pa-orthogonal plus ambient-outside inventory. -/
theorem actual_nonPa_source_inventory (h : ℝ) :
    actualNonPaSource observation nontrivial half h =
      O (OriginalKFullSourceRResponse.completeSource observation nontrivial half h) +
      ((OriginalKFullSourceRResponse.sourceResidual observation nontrivial half h : BurnolPaAmbientCarrier) : BurnolL2) := by
  let source := OriginalKFullSourceRResponse.completeSource observation nontrivial half h
  have pa := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (P source)
  have paRaw := congrArg (fun x : BurnolPaAmbientCarrier => (x : BurnolL2)) pa
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal source
  change (E source : BurnolL2) + (Q source : BurnolL2) = (P source : BurnolL2) at paRaw
  change (P source : BurnolL2) + O source = source at physical
  rw [OriginalKFullSourceRResponse.source_residual_read]
  change source - (E source : BurnolL2) = O source + (Q source : BurnolL2)
  linear_combination (norm := module) -physical - paRaw

/-- Both retained nonPa pieces are acted on by the original R before their target readers. -/
theorem actual_nonPa_R_inventory (h : ℝ) :
    actualNonPaR observation nontrivial half h =
      OriginalKFullSourceRResponse.Op.R observation nontrivial half
        (O (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) +
      OriginalKFullSourceRResponse.Op.R observation nontrivial half
        ((OriginalKFullSourceRResponse.sourceResidual observation nontrivial half h : BurnolPaAmbientCarrier) : BurnolL2) := by
  unfold actualNonPaR
  rw [actual_nonPa_source_inventory,map_add]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
