import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace AP
export OriginalKWindowInverseResidualSourceAction.AP (AdmissionPacket bornAfterNative)
end AP
namespace Transport
export ActualCofinalSourceAction (packetTransport)
end Transport
namespace PaRoot
export OriginalKWindowInverseResidualSourceAction (actualSourceFactory actualResidualPacket)
end PaRoot
local instance packetSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (source : Branches) (shift : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

abbrev sourceSelectedAt := stockSelected source shift producer
 packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down
abbrev sourceBaseAt := sourceEmitterBase source shift
 (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down

def sourceNativePacket : AP.AdmissionPacket (W:=PairValue C.Value) (X:=packet.2.2.1.LowVar) (s:=()) :=
 ⟨packet.1+1,⟨AS.receiver (splitFactory producer)
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
  AS.nextSeed (splitFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
  sourceBaseAt source shift producer packet,⟨rfl⟩⟩

def sourceBornPacket : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()) :=
 Transport.packetTransport packet.2.2.2.down (AP.bornAfterNative
  (sourceNativePacket source shift producer packet))

theorem source_packet_full_history (auxiliary : OriginalKBoundaryNextActualSourceDelta.SF.Seed
 (L.Value (PairValue C.Value) (sourceBornPacket source shift producer packet).1) C.Var () 0) :
 type_of% (OriginalKBoundaryNextActualSourceDelta.exact_packet_history_successor (splitFactory producer)
  (sourceBornPacket source shift producer packet) auxiliary) :=
 OriginalKBoundaryNextActualSourceDelta.exact_packet_history_successor _ _ _

theorem source_packet_all_future (futureOrdinal : Nat) (history : List PUnit) (target : Nat) :
 type_of% (OriginalKBoundaryNextActualSourceDelta.packet_all_future (splitFactory producer)
  (sourceBornPacket source shift producer packet) futureOrdinal history target) :=
 OriginalKBoundaryNextActualSourceDelta.packet_all_future _ _ _ _ _

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N radius : ℝ)

/-- The complete actual227 born packet is the next source occurrence, retaining its seed and both trace inventories. -/
abbrev actualParentFactory := OriginalKDecodedPaRFourFaceSourceAction.fourFaceFactory
 (originalSourceFactory observation nontrivial half depth ordinal h)
abbrev actualParentPacket := OriginalKDecodedPaRFourFaceSourceAction.sourceBornPacket observation nontrivial half depth ordinal h H N
 (originalSourceFactory observation nontrivial half depth ordinal h)
 (originalSourcePacket observation nontrivial half depth ordinal h H N radius)

attribute [irreducible] sourceNativePacket sourceBornPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
