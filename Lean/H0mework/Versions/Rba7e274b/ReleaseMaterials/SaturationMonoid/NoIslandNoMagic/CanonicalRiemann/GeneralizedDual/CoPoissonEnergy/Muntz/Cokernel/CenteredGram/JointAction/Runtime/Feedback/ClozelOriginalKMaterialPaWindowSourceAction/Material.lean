import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Parent
export OriginalKBoundaryNextActualSourceDelta (actualParentPacket actualNextPacket)
end Parent
namespace Original
export OriginalKBoundaryNextActualSourceDelta.Parent (factory)
end Original
local instance paMaterialJoinGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

abbrev actualParentBornPacket := Parent.actualNextPacket observation nontrivial half depth ordinal h H N
abbrev actualParentRFactory := OriginalKWholePaNativeRankSourceUpdate.actualSourceRActorFactory observation nontrivial half
 (Original.factory observation nontrivial half depth ordinal h)

def materialRAt (observation : GeneratedRiemannZeroObservation)
 (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1)) (half : OriginalKCombCalculation.Half observation)
 (factory : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) (H N : ℝ) : D.SourceBranches :=
 D.actualMaterialREffect observation nontrivial half factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N
attribute [irreducible] materialRAt

def actualParentMaterialREffect : D.SourceBranches :=
 materialRAt observation nontrivial half (Original.factory observation nontrivial half depth ordinal h)
  (Parent.actualParentPacket observation nontrivial half depth ordinal h) H N

def actualPaBornPacket := paBornPacket
 (actualParentRFactory observation nontrivial half depth ordinal h)
 (actualParentBornPacket observation nontrivial half depth ordinal h H N)
 (actualParentMaterialREffect observation nontrivial half depth ordinal h H N)

theorem actual_Pa_material_whole : type_of%
 (paWholeAt (actualParentRFactory observation nontrivial half depth ordinal h)
  (actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (actualParentMaterialREffect observation nontrivial half depth ordinal h H N)).actual_step :=
 (paWholeAt _ _ _).actual_step

theorem actual_Pa_material_next : type_of%
 (pa_whole_next (actualParentRFactory observation nontrivial half depth ordinal h)
  (actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (actualParentMaterialREffect observation nontrivial half depth ordinal h H N)) := pa_whole_next _ _ _

theorem actual_Pa_material_all_future (futureOrdinal : Nat) (history : List PUnit) (target : Nat) : type_of%
 (pa_packet_all_future (actualParentRFactory observation nontrivial half depth ordinal h)
  (actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (actualParentMaterialREffect observation nontrivial half depth ordinal h H N) futureOrdinal history target) :=
 pa_packet_all_future _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
