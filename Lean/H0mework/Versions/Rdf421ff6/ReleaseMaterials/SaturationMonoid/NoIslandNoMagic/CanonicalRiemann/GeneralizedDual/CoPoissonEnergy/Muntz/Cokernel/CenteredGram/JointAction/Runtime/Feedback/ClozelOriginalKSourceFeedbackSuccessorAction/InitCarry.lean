import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitInstalled
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitJoin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
local instance carryGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target


private theorem packet_scalar_has_transport {Y Z : Unit → Type} (same : Y=Z)
 (source : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=()))
 (has : source.2.1.1.inventory.isSome) : (NT.packetTransport same source).2.1.1.inventory.isSome := by
 cases same
 exact has

private theorem packet_pair_has_transport {Y Z : Unit → Type} (same : Y=Z)
 (source : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=()))
 (has : source.2.1.1.pairInventory.isSome) : (NT.packetTransport same source).2.1.1.pairInventory.isSome := by
 cases same
 exact has

private theorem packet_scalar_members_transport {Y Z : Unit → Type} (same : Y=Z)
 (source : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=()))
 (targetPacket : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Z) (s:=()))
 (samePacket : targetPacket=NT.packetTransport same source)
 (has : source.2.1.1.inventory.isSome) (event)
 (present : event∈(source.2.1.1.inventory.get has).trace) :
 ∃ transportedEvent, transportedEvent∈(targetPacket.2.1.1.inventory.get
  (by rw [samePacket]; exact packet_scalar_has_transport same source has)).trace ∧ HEq transportedEvent event := by
 cases samePacket
 cases same
 exact ⟨event,present,HEq.rfl⟩

private theorem packet_pair_members_transport {Y Z : Unit → Type} (same : Y=Z)
 (source : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=()))
 (targetPacket : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Z) (s:=()))
 (samePacket : targetPacket=NT.packetTransport same source)
 (has : source.2.1.1.pairInventory.isSome) (event)
 (present : event∈(source.2.1.1.pairInventory.get has).trace) :
 ∃ transportedEvent, transportedEvent∈(targetPacket.2.1.1.pairInventory.get
  (by rw [samePacket]; exact packet_pair_has_transport same source has)).trace ∧ HEq transportedEvent event := by
 cases samePacket
 cases same
 exact ⟨event,present,HEq.rfl⟩

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance carryNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target

/-- Actual initializer nodes are transported with the whole native packet, then retained by the same successor stock. -/
theorem actual_init_scalar_nodes_in_successor
 (event : PresentedRelationEventAt (Expr (L.Value (PairValue C.Value) (packet.1+1)) packet.2.2.1.LowVar ()))
 (present : event∈((sourceInitBorn t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).inventory.get (by rfl)).trace) :
 ∃ transportedEvent, transportedEvent∈((actualNextSourceFrame t factory packet).inventory.get (by rfl)).trace ∧ HEq transportedEvent event := by
 let native:=AP.bornAfterNative (sourceInitNativePacket t factory packet)
 have nativeHas : native.2.1.1.inventory.isSome := by
  unfold native AP.bornAfterNative sourceInitNativePacket
  rfl
 have sourceMember : ∃ sourceEvent, sourceEvent∈(native.2.1.1.inventory.get nativeHas).trace ∧ HEq sourceEvent event := by
  unfold native AP.bornAfterNative sourceInitNativePacket
  exact ⟨event,present,HEq.rfl⟩
 rcases sourceMember with ⟨sourceEvent,member,same⟩
 have bornEq : sourceInitBornPacket t factory packet=NT.packetTransport packet.2.2.2.down native := by
  unfold sourceInitBornPacket
  rfl
 have beforeHas : (sourceNextFrame t factory packet).inventory.isSome := by
  change (sourceInitBornPacket t factory packet).2.1.1.inventory.isSome
  rw [bornEq]
  exact packet_scalar_has_transport _ _ nativeHas
 rcases packet_scalar_members_transport packet.2.2.2.down native (sourceInitBornPacket t factory packet) bornEq nativeHas sourceEvent member with ⟨actualEvent,atFrame,transport⟩
 have carried : actualEvent∈((sourceNextFrame t factory packet).inventory.get beforeHas).trace := by
  exact atFrame
 refine ⟨actualEvent,?_,transport.trans same⟩
 let old:=(sourceNextFrame t factory packet).inventory.get beforeHas
 exact actual_source_old_scalar_in_born (actualNestedSourceBinding t factory packet) ()
  (sourceActualContinuation t factory packet) 0 (sourceInitBornPacket t factory packet).2.1.2
  (sourceNextFrame t factory packet) old (Option.some_get beforeHas).symm actualEvent carried

/-- The corresponding complete paired words pass the same actual packet language and grade transport. -/
theorem actual_init_pair_nodes_in_successor
 (event : PresentedRelationEventAt (Expr (PairValue (L.Value (PairValue C.Value) (packet.1+1))) packet.2.2.1.LowVar ()))
 (present : event∈((sourceInitBorn t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down).pairInventory.get (by rfl)).trace) :
 ∃ transportedEvent, transportedEvent∈((actualNextSourceFrame t factory packet).pairInventory.get (by rfl)).trace ∧ HEq transportedEvent event := by
 let native:=AP.bornAfterNative (sourceInitNativePacket t factory packet)
 have nativeHas : native.2.1.1.pairInventory.isSome := by
  unfold native AP.bornAfterNative sourceInitNativePacket
  rfl
 have sourceMember : ∃ sourceEvent, sourceEvent∈(native.2.1.1.pairInventory.get nativeHas).trace ∧ HEq sourceEvent event := by
  unfold native AP.bornAfterNative sourceInitNativePacket
  exact ⟨event,present,HEq.rfl⟩
 rcases sourceMember with ⟨sourceEvent,member,same⟩
 have bornEq : sourceInitBornPacket t factory packet=NT.packetTransport packet.2.2.2.down native := by
  unfold sourceInitBornPacket
  rfl
 have beforeHas : (sourceNextFrame t factory packet).pairInventory.isSome := by
  change (sourceInitBornPacket t factory packet).2.1.1.pairInventory.isSome
  rw [bornEq]
  exact packet_pair_has_transport _ _ nativeHas
 rcases packet_pair_members_transport packet.2.2.2.down native (sourceInitBornPacket t factory packet) bornEq nativeHas sourceEvent member with ⟨actualEvent,atFrame,transport⟩
 have carried : actualEvent∈((sourceNextFrame t factory packet).pairInventory.get beforeHas).trace := by
  exact atFrame
 refine ⟨actualEvent,?_,transport.trans same⟩
 let old:=(sourceNextFrame t factory packet).pairInventory.get beforeHas
 exact actual_source_old_pair_in_born (actualNestedSourceBinding t factory packet) ()
  (sourceActualContinuation t factory packet) 0 (sourceInitBornPacket t factory packet).2.1.2
  (sourceNextFrame t factory packet) old (Option.some_get beforeHas).symm actualEvent carried
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
