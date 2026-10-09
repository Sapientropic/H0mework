import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))

theorem same_root : (state frame configuration).root=(old frame configuration).root := rfl
theorem same_visit : (state frame configuration).visit=(old frame configuration).visit := rfl
theorem same_query : (state frame configuration).Query=(old frame configuration).Query := rfl
theorem same_entry (candidate : (old frame configuration).Query) :
 (state frame configuration).entryAt candidate=(old frame configuration).entryAt candidate := rfl
theorem same_authority (candidate : (old frame configuration).Query) :
 HEq ((state frame configuration).authorityAt candidate) ((old frame configuration).authorityAt candidate) := HEq.rfl

theorem receiver_current : (lowInitial frame configuration).currentState=SourceGeneratedInquiryReceiptAction.targetState frame configuration := rfl
theorem receiver_inventory : (lowInitial frame configuration).inventory=some (lowWritten frame configuration) := rfl
theorem receiver_pair_inventory : (lowInitial frame configuration).pairInventory=some (lowPairWritten frame configuration) := rfl

theorem target_root (event : Event frame configuration) :
 (targetAt frame configuration event).targetRoot=A.Shared.root (lowInitial frame configuration) (lowProgramme frame configuration) := rfl

theorem target_next (event : Event frame configuration) :
 (targetAt frame configuration event).targetAnswerAndNext.nextCurrent =
 ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
   (lowInitial frame configuration).registered (lowInitial frame configuration).packetAt,
  (A.Shared.root (lowInitial frame configuration) (lowProgramme frame configuration)).toAuthoritativeRoot,
  A.Shared.visit (lowInitial frame configuration) (lowProgramme frame configuration)⟩ := by
 change (A.Shared.root (lowInitial frame configuration) (lowProgramme frame configuration)).generatedNextCurrentAt
  (.finite (A.Shared.root (lowInitial frame configuration) (lowProgramme frame configuration)).toAuthoritativeRoot.toRoot.initialVisit) = _
 apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
 rfl

theorem compiles : (state frame configuration).compileInquiry (A.Shared.query frame configuration) =
 .debtAdmission (generatedAction frame configuration) := rfl

theorem successor_valid : (targetPresentation frame configuration).erase =
 (RootInquiryProcessNode.answered (sourcePresentation frame configuration) (A.Shared.query frame configuration)).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation frame configuration)).PreservesGeneratedLivingLawAt
  (A.Shared.query frame configuration) (.active (targetPresentation frame configuration)) := by
 apply RootInquiryProcessNode.active_debtAdmission_successor_valid
  (sourcePresentation frame configuration) (targetPresentation frame configuration)
  (A.Shared.query frame configuration) (generatedAction frame configuration) (compiles frame configuration)
 · exact (congrArg (fun current =>
    (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World (lowInitial frame configuration).registered,current⟩ :
      AnyAuthoritativeRootCurrent.{u})) (target_next frame configuration (sourceEvent frame configuration))).symm
 · exact HEq.rfl

theorem actual_initial : (lowRuntime frame configuration).initialState.engine.node =
 .active (targetPresentation frame configuration) := rfl

theorem runtime_source_gate : ((lowRuntime frame configuration).initialState.engine.node).erase =
 (RootInquiryProcessNode.answered (sourcePresentation frame configuration) (A.Shared.query frame configuration)).erase ∧
 (RootInquiryProcessNode.active (sourcePresentation frame configuration)).PreservesGeneratedLivingLawAt
 (A.Shared.query frame configuration) ((lowRuntime frame configuration).initialState.engine.node) := by
 rw [actual_initial]
 exact successor_valid frame configuration

theorem whole_first (event : Event frame configuration) : type_of% (targetAt frame configuration event).firstDestination_heq :=
 (targetAt frame configuration event).firstDestination_heq

theorem old_outcome (event : Event frame configuration)
 (projection : (old frame configuration).root.toAuthoritativeRoot.source.projectionLaw.Projection) :
 type_of% ((targetAt frame configuration event).oldOutcome_heq projection) :=
 (targetAt frame configuration event).oldOutcome_heq projection

theorem first_successor_preserved (event : Event frame configuration) :
 HEq (targetAt frame configuration event).firstSuccessor
 ((SourceGeneratedInquiryReceiptAction.birthProgram frame configuration).targetAt event).firstSuccessor := HEq.rfl

theorem answer_preserved (event : Event frame configuration) :
 HEq (targetAt frame configuration event).answer
 ((SourceGeneratedInquiryReceiptAction.birthProgram frame configuration).targetAt event).answer := HEq.rfl

theorem receipt_preserved (event : Event frame configuration) :
 HEq (targetAt frame configuration event).receipt
 ((SourceGeneratedInquiryReceiptAction.birthProgram frame configuration).targetAt event).receipt := HEq.rfl

theorem main_event_preserved (event) (present : event ∈ (lowStock frame configuration).trace) :
 event ∈ (lowWritten frame configuration).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem outgoing_event_preserved (event) (present : event ∈ (outgoingScalar frame configuration).trace) :
 event ∈ (lowWritten frame configuration).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem main_seed_preserved (event) (present : event ∈ (lowWritten frame configuration).trace) :
 event ∈ (lowSeed frame configuration).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem pair_event_preserved (event) (present : event ∈ (outgoingPair frame configuration).trace) :
 event ∈ (lowPairWritten frame configuration).trace := by
 unfold lowPairWritten
 cases (lowBareInitial frame configuration).pairInventory with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

theorem actual_query (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.actual_input
  (lowSeed frame configuration) (lowInitial frame configuration) offset) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.actual_input _ _ _
theorem actual_answer (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.actual_answer
  (lowSeed frame configuration) (lowInitial frame configuration) offset) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.actual_answer _ _ _
theorem actual_next (offset : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.actual_next
  (lowSeed frame configuration) (lowInitial frame configuration) offset) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.actual_next _ _ _

end SourceGeneratedInquiryReceiptAction.Configured
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
