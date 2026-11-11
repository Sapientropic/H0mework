import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceEnergy.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceEnergy
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance sourceEnergyPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

theorem source_R_physical : sourceR observation nontrivial half depth ordinal h H N ∈
 evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 rw [source_R_read]
 exact OriginalKDecodedPaRSourceSuccessor.own_source_R_physical observation nontrivial half depth ordinal h H N

def physicalSourceR : BurnolPaAmbientCarrier :=
 ⟨sourceR observation nontrivial half depth ordinal h H N,source_R_physical observation nontrivial half depth ordinal h H N⟩
def PaSourceR : BurnolPaAmbientCarrier := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
 (physicalSourceR observation nontrivial half depth ordinal h H N)
def unitRankSourceR : BurnolPaAmbientCarrier := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
 (physicalSourceR observation nontrivial half depth ordinal h H N)

/-- Both orthogonal costs come from this physical source occurrence's projection, with no component deleted. -/
theorem source_R_complete_Gram : ‖sourceR observation nontrivial half depth ordinal h H N‖^2 =
 ‖PaSourceR observation nontrivial half depth ordinal h H N‖^2+
 ‖unitRankSourceR observation nontrivial half depth ordinal h H N‖^2 :=
 Submodule.norm_sq_eq_add_norm_sq_starProjection
  (physicalSourceR observation nontrivial half depth ordinal h H N) burnolCompactCoPoissonClosedRange.toSubmodule

theorem source_Pa_inner_read :
 inner ℂ (PaSourceR observation nontrivial half depth ordinal h H N)
  (OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N).val =
 inner ℂ (sourceR observation nontrivial half depth ordinal h H N)
  (Four.sourceA observation nontrivial half depth ordinal h H N) := by
 have generated := burnolCompactCoPoissonClosedRange.toSubmodule.inner_starProjection_left_eq_right
  (physicalSourceR observation nontrivial half depth ordinal h H N)
  (OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N).val
 rw [burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr
  (OriginalKDecodedPaRSourceSuccessor.decoded_pa_source_qualified observation nontrivial half depth ordinal h H N)] at generated
 exact generated

/-- The source action pays the full Pa plus rank debt rather than forcing the rank cost to vanish. -/
theorem source_Pa_complete_energy :
 -(inner ℂ (PaSourceR observation nontrivial half depth ordinal h H N)
  (OriginalKDecodedPaRSourceSuccessor.decodedPaSource observation nontrivial half depth ordinal h H N).val).re =
 (observation.coordinate/2-1/4).re *
  (‖PaSourceR observation nontrivial half depth ordinal h H N‖^2+
   ‖unitRankSourceR observation nontrivial half depth ordinal h H N‖^2) := by
 rw [source_Pa_inner_read,source_R_energy,source_R_complete_Gram]
 ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
