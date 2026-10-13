import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Whole
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance finiteMaterialJoinGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

/-- Read the exact preceding Pa source write, keeping its complete packet separate from its source quantity. -/
def previousNuAt (factory : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) (material : Branches) : BurnolL2 :=
 OriginalKMaterialPaWindowSourceAction.receivedPaSource factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down material
  (packet.2.2.2.down.symm ▸ ())
attribute [irreducible] previousNuAt

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

abbrev actualPreviousFactory := OriginalKMaterialPaWindowSourceAction.actualParentRFactory observation nontrivial half depth ordinal h
abbrev actualPreviousPacket := OriginalKMaterialPaWindowSourceAction.actualPaBornPacket observation nontrivial half depth ordinal h H N

def actualReceivedNu : Branches := Native.sourceFields
 (previousNuAt (actualPreviousFactory observation nontrivial half depth ordinal h)
  (OriginalKMaterialPaWindowSourceAction.actualParentBornPacket observation nontrivial half depth ordinal h H N)
  (OriginalKMaterialPaWindowSourceAction.actualParentMaterialREffect observation nontrivial half depth ordinal h H N))

def actualFinitePacket := finiteBornPacket (actualPreviousFactory observation nontrivial half depth ordinal h)
 (actualPreviousPacket observation nontrivial half depth ordinal h H N) radius
 (actualReceivedNu observation nontrivial half depth ordinal h H N)

theorem actual_finite_whole : type_of% (finiteWholeAt (actualPreviousFactory observation nontrivial half depth ordinal h)
 (actualPreviousPacket observation nontrivial half depth ordinal h H N) radius
 (actualReceivedNu observation nontrivial half depth ordinal h H N)).actual_step := (finiteWholeAt _ _ _ _).actual_step

theorem actual_finite_all_future (futureOrdinal : Nat) (history : List PUnit) (target : Nat) : type_of%
 (finite_packet_all_future (actualPreviousFactory observation nontrivial half depth ordinal h)
  (actualPreviousPacket observation nontrivial half depth ordinal h H N) radius
  (actualReceivedNu observation nontrivial half depth ordinal h H N) futureOrdinal history target) :=
 finite_packet_all_future _ _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
