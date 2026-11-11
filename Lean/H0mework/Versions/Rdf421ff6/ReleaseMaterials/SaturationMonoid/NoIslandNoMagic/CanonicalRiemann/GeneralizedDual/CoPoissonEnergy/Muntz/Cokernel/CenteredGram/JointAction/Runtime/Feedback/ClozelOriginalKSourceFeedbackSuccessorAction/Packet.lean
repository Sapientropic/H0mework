import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitInventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Future.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace AP
export OriginalKFullSourceRAction.AS (AdmissionPacket bornAfterNative)
end AP
namespace Receiver
export OriginalKMaterialPhysicalStockSourceAction.Receiver (receiver nextSeed)
end Receiver
namespace NT
export ActualCofinalSourceAction (sourceBorn packetTransport)
end NT
namespace Future
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed actual_source_seed_callbacks)
end Future
local instance packetGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

/-- This actual initialization changes the original decoder before the existing emitter receives its first raw-slots source packet. -/
def sourceInitNativePacket : AP.AdmissionPacket (W:=PairValue C.Value) (X:=packet.2.2.1.LowVar) (s:=()) :=
 ⟨packet.1+1,
 ⟨Receiver.receiver (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
 Receiver.nextSeed (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
 sourceSlotInitStockBase t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
 ⟨rfl⟩⟩

def sourceInitBornPacket : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()) :=
 NT.packetTransport packet.2.2.2.down (AP.bornAfterNative (sourceInitNativePacket t factory packet))

private theorem packet_transport_grade {Y Z : Unit → Type} (same : Y=Z)
 (source : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=())) :
 (NT.packetTransport same source).1=source.1 := by
 cases same
 rfl

/-- Exact source packet transport preserves its actual nested grade. -/
theorem source_init_born_grade : (sourceInitBornPacket t factory packet).1=packet.1+1 := by
 unfold sourceInitBornPacket
 rw [packet_transport_grade]
 unfold AP.bornAfterNative sourceInitNativePacket
 rfl

/-- No grade is reset: this is the existing exact nested source carrier and its inherited callbacks. -/
def sourceActualContinuation :=
 Future.fromSourceSeed
  (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) C.Var ()
  (Future.continuationFactory (PairValue C.Value) C.Var ()
   (actualSourceSlotSuccessorFactory factory) (sourceInitBornPacket t factory packet).1)
  (sourceInitBornPacket t factory packet).2.1.2

/-- The same actual initialization seed, not a freely rebuilt root, starts every relative callback. -/
theorem actual_source_seed_callbacks (suppliedSeed) : type_of%
 (Future.actual_source_seed_callbacks
  (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) C.Var ()
  (Future.continuationFactory (PairValue C.Value) C.Var ()
   (actualSourceSlotSuccessorFactory factory) (sourceInitBornPacket t factory packet).1)
  (sourceInitBornPacket t factory packet).2.1.2 suppliedSeed
  (sourceInitBornPacket t factory packet).2.1.1) :=
 Future.actual_source_seed_callbacks _ _ _ _ _ _ _

attribute [irreducible] sourceInitNativePacket sourceInitBornPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
