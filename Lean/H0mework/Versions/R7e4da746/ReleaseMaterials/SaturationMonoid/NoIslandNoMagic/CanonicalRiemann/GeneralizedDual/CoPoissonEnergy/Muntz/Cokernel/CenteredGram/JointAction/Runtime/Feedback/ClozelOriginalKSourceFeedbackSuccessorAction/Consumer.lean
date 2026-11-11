import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.OriginalFee
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
local instance mainGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target


variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance mainNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target
variable (suppliedSeed : Mother.SF.Seed (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) C.Var () 0)
variable (bornCurrent)
variable (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent)

/-- Actual initialization, literal tail-driven update, typed word inventories and the canonical whole step jointly feed the original expanded fees. The mathematical ordinal is read after the source action. -/
theorem main :
 (type_of% (actual_source_before_is_generated_initial t factory packet)) ∧
 (type_of% (actual_source_after_is_generated_first t factory packet bornCurrent occurrence)) ∧
 (type_of% (actual_original_expanded_fees t factory packet bornCurrent occurrence)) ∧
 (type_of% (actual_original_received_tail_budget t factory packet bornCurrent occurrence)) ∧
 (∀ raw : FeedbackFeet, type_of% (source_feedback_whole_conserved raw)) ∧
 (type_of% (actual_whole_source_raw_successor t factory packet bornCurrent occurrence)) ∧
 (type_of% (actual_whole_source_tail_bound t factory packet bornCurrent occurrence)) ∧
 (type_of% (actual_source_seed_callbacks t factory packet suppliedSeed)) ∧
 (∀ event (_present : event∈(SourceOperationPaidRelations.exposure
  (sourceActualTrace (actualNestedSourceBinding t factory packet) () 0 (sourceNextFrame t factory packet))).trace),
  event∈((actualNextSourceFrame t factory packet).inventory.get (by rfl)).trace) ∧
 (∀ event (_present : event∈(SourceOperationPaidRelations.exposure
  (sourceActualScalarTrace (actualNestedSourceBinding t factory packet) () 0 (sourceNextFrame t factory packet))).trace),
  event∈((actualNextSourceFrame t factory packet).pairInventory.get (by rfl)).trace) ∧
 (∀ prior (_actual : (sourceNextFrame t factory packet).inventory=some prior) event (_present : event∈prior.trace),
  event∈((actualNextSourceFrame t factory packet).inventory.get (by rfl)).trace) ∧
 (∀ prior (_actual : (sourceNextFrame t factory packet).pairInventory=some prior) event (_present : event∈prior.trace),
  event∈((actualNextSourceFrame t factory packet).pairInventory.get (by rfl)).trace) ∧
 (∀ (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (_installed : code∈sourceInitInventoryCodes t)
  event (_present : event∈(SourceOperationPaidRelations.exposure
   (sourceInitQueryTrace (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down code
    (sourceInitSelected t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down))).trace),
  ∃ transportedEvent, transportedEvent∈((actualNextSourceFrame t factory packet).inventory.get (by rfl)).trace ∧ HEq transportedEvent event) ∧
 (∀ (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (_installed : code∈sourceInitInventoryCodes t)
  event (_present : event∈(SourceOperationPaidRelations.exposure
   (sourceInitQueryPairTrace (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down code
    (sourceInitSelected t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down))).trace),
  ∃ transportedEvent, transportedEvent∈((actualNextSourceFrame t factory packet).pairInventory.get (by rfl)).trace ∧ HEq transportedEvent event) ∧
 (type_of% ((actualSourceNextWhole t factory packet).actual_step)) ∧
 (type_of% ((actualSourceNextWhole t factory packet).same_ledger)) ∧
 (type_of% ((actualSourceNextWhole t factory packet).same_visit)) ∧
 (type_of% ((actualSourceNextWhole t factory packet).payment.strictDebit)) ∧
 (type_of% ((actualSourceNextWhole t factory packet).entry)) ∧
 (type_of% ((actualSourceNextWhole t factory packet).whole_destination)) ∧
 (type_of% (actual_source_whole_root t factory packet)) ∧
 (type_of% (actual_source_whole_current t factory packet)) :=
 ⟨actual_source_before_is_generated_initial t factory packet,
 actual_source_after_is_generated_first t factory packet bornCurrent occurrence,
 actual_original_expanded_fees t factory packet bornCurrent occurrence,
 actual_original_received_tail_budget t factory packet bornCurrent occurrence,
 fun raw => source_feedback_whole_conserved raw,
 actual_whole_source_raw_successor t factory packet bornCurrent occurrence,
 actual_whole_source_tail_bound t factory packet bornCurrent occurrence,
 actual_source_seed_callbacks t factory packet suppliedSeed,
 fun event present => actual_source_scalar_trace_in_born
  (actualNestedSourceBinding t factory packet) () (sourceActualContinuation t factory packet) 0
  (sourceInitBornPacket t factory packet).2.1.2 (sourceNextFrame t factory packet) event present,
 fun event present => actual_source_pair_trace_in_born
  (actualNestedSourceBinding t factory packet) () (sourceActualContinuation t factory packet) 0
  (sourceInitBornPacket t factory packet).2.1.2 (sourceNextFrame t factory packet) event present,
 fun prior actual event present => actual_source_old_scalar_in_born
  (actualNestedSourceBinding t factory packet) () (sourceActualContinuation t factory packet) 0
  (sourceInitBornPacket t factory packet).2.1.2 (sourceNextFrame t factory packet) prior actual event present,
 fun prior actual event present => actual_source_old_pair_in_born
  (actualNestedSourceBinding t factory packet) () (sourceActualContinuation t factory packet) 0
  (sourceInitBornPacket t factory packet).2.1.2 (sourceNextFrame t factory packet) prior actual event present,
 fun code installed event present => actual_init_scalar_nodes_in_successor t factory packet event
  (actual_init_scalar_nodes_in_born t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down code installed event present),
 fun code installed event present => actual_init_pair_nodes_in_successor t factory packet event
  (actual_init_pair_nodes_in_born t (actualSourceSlotSuccessorFactory factory) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down code installed event present),
 (actualSourceNextWhole t factory packet).actual_step,
 (actualSourceNextWhole t factory packet).same_ledger,
 (actualSourceNextWhole t factory packet).same_visit,
 (actualSourceNextWhole t factory packet).payment.strictDebit,
 (actualSourceNextWhole t factory packet).entry,
 (actualSourceNextWhole t factory packet).whole_destination,
 actual_source_whole_root t factory packet,
 actual_source_whole_current t factory packet⟩
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
