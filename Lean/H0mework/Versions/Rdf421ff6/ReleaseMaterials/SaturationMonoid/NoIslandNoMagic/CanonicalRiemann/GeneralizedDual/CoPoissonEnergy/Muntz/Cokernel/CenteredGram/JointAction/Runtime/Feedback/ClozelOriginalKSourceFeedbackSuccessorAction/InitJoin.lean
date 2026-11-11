import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Packet
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitBorn
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
local instance joinGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem packet_frame_transport {Y Z : Unit → Type} (same : Y=Z)
 (source : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=())) :
 HEq (NT.packetTransport same source).2.1.1 source.2.1.1 := by
 cases same
 exact HEq.rfl

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

/-- The initializer's actual whole born frame is the original packet's frame after its genuine language transport. -/
theorem source_init_packet_actual_frame :
 HEq (sourceInitBornPacket t factory packet).2.1.1
 (sourceInitBorn t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down) := by
 unfold sourceInitBornPacket
 exact (packet_frame_transport _ _).trans (show
  HEq (AP.bornAfterNative (sourceInitNativePacket t factory packet)).2.1.1
   (sourceInitBorn t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down) from by
   dsimp only [AP.bornAfterNative,
    SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.localNativeReceipt,
    sourceInitBorn,sourceInitSelected,Complete.atReceipt]
   unfold sourceInitNativePacket
   rfl)

/-- This source context retains the complete old-paid/native total as a different role from its generated raw slots. -/
def actualInitSourceTotal : Prior.Branches := CF.collapseValue packet.1
 (sourceInitUpdatedValue t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down)

def actualInitQuarterSource := sourceExpandedQuarterReader t (originalField (actualInitSourceTotal t factory packet))

theorem source_init_original_raw_mouth (name : packet.2.2.1.LowVar ()) :
 CF.collapseValue packet.1
  ((sourceInitBorn t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).activeEnvironment () name)=
 sourceRawSlots (sourceRawFeet (actualInitQuarterSource t factory packet) 0) :=
 source_init_born_raw_slots _ _ _ _ _ _ _
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
