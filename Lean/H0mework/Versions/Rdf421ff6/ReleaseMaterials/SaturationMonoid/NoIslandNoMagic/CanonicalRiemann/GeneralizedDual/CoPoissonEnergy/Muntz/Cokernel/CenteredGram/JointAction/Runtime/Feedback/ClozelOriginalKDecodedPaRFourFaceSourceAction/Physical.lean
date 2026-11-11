import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Op
export OriginalKCombPhysicalAction (R)
end Op
namespace Ward
export OriginalKCombCofinalPaAction (paired sibling ambient_R_paired_equations)
end Ward
local instance ownPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

abbrev sourceA : BurnolL2 := (Prior.decodedPaSource observation nontrivial half depth ordinal h H N).val

/-- These are the four outputs of the literal operation, including both actual source contact terms. -/
theorem own_four_face_read : ownFourFaceSource observation nontrivial half depth ordinal h H N =
 ((Ward.paired (Op.R observation nontrivial half (sourceA observation nontrivial half depth ordinal h H N)),
   Ward.sibling (Op.R observation nontrivial half (sourceA observation nontrivial half depth ordinal h H N))),
  ((observation.coordinate/2-1/4) • Ward.sibling (Op.R observation nontrivial half (sourceA observation nontrivial half depth ordinal h H N)) +
    (1/2 : ℂ) • (sourceA observation nontrivial half depth ordinal h H N-fourierL2 (sourceA observation nontrivial half depth ordinal h H N)),
   (observation.coordinate/2-1/4) • Ward.paired (Op.R observation nontrivial half (sourceA observation nontrivial half depth ordinal h H N)) +
    (1/2 : ℂ) • (sourceA observation nontrivial half depth ordinal h H N+fourierL2 (sourceA observation nontrivial half depth ordinal h H N)))) := by
 let a := sourceA observation nontrivial half depth ordinal h H N
 let r := Op.R observation nontrivial half a
 let p := Ward.paired r
 let q := Ward.sibling r
 change ((p+0,q+0),
  ((observation.coordinate/2-1/4) • q + (1/2 : ℂ) • (a-fourierL2 a),
   (observation.coordinate/2-1/4) • p + (1/2 : ℂ) • (a+fourierL2 a))) =
  ((p,q),((observation.coordinate/2-1/4) • q + (1/2 : ℂ) • (a-fourierL2 a),
   (observation.coordinate/2-1/4) • p + (1/2 : ℂ) • (a+fourierL2 a)))
 simp only [add_zero]

/-- The two velocities come from the original source R action law, not by relabelling DR. -/
theorem own_source_ward_action :
 HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
  (ownFourFaceSource observation nontrivial half depth ordinal h H N).1.1)
  (ownFourFaceSource observation nontrivial half depth ordinal h H N).2.1 0 ∧
 HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
  (ownFourFaceSource observation nontrivial half depth ordinal h H N).1.2)
  (ownFourFaceSource observation nontrivial half depth ordinal h H N).2.2 0 := by
 rw [own_four_face_read]
 dsimp only
 rw [OriginalKCombCofinalRAction.original_R_direct]
 exact Ward.ambient_R_paired_equations _ (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) _

theorem own_four_faces_physical :
 (ownFourFaceSource observation nontrivial half depth ordinal h H N).1.1 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
 (ownFourFaceSource observation nontrivial half depth ordinal h H N).1.2 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
 (ownFourFaceSource observation nontrivial half depth ordinal h H N).2.1 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
 (ownFourFaceSource observation nontrivial half depth ordinal h H N).2.2 ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
 let face := evenBurnolClosedFace burnolUnscaledCommonGapRadius
 have r := OriginalKDecodedPaRSourceSuccessor.own_source_R_physical observation nontrivial half depth ordinal h H N
 change Op.R observation nontrivial half (sourceA observation nontrivial half depth ordinal h H N) ∈ face at r
 have fr := fourierL2_mem_evenBurnolClosedFace r
 have a : sourceA observation nontrivial half depth ordinal h H N ∈ face :=
  (Prior.decodedPaSource observation nontrivial half depth ordinal h H N).val.property
 have fa := fourierL2_mem_evenBurnolClosedFace a
 have pair := face.smul_mem (1/2 : ℂ) (face.add_mem r fr)
 have sibling := face.smul_mem (1/2 : ℂ) (face.sub_mem r fr)
 rw [own_four_face_read]
 exact ⟨pair,sibling,
  face.add_mem (face.smul_mem _ sibling) (face.smul_mem _ (face.sub_mem a fa)),
  face.add_mem (face.smul_mem _ pair) (face.smul_mem _ (face.add_mem a fa))⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
