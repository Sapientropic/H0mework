import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Next.Source
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Primary.FourFace
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.Primary.FourFace
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.PrimaryConsumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Next.PursuitConsumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.Effect
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.RichConsumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Continuation.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.Consumer
import Lean.LibrarySuggestions.Basic
-- Large dependent runtime mouths are used directly by their consumers.
run_cmd Lean.modifyEnv fun env => ["branch_actor_value", "branch_actor_source", "branch_actor_registered", "branch_actor_order", "branch_actor_stock", "branch_actor_disposition", "branch_actor_query", "branch_actor_input", "branch_actor_result", "branch_actor_next", "branch_actor_born", "branch_actor_equation", "branch_actor_trace", "branch_actor_faces", "branch_actor_born_whole", "branch_actor_born_next"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_live_binding", "branch_live_query", "branch_live_next", "branch_live_answer", "branch_live_faces", "branch_live_equation", "branch_live_inverse", "branch_live_inverse_whole", "branch_live_inverse_next", "branch_live_payment"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_operation_registered", "branch_operation_source", "branch_operation_stock", "branch_operation_disposition", "branch_operation_query", "branch_operation_input", "branch_operation_result", "branch_operation_next", "branch_operation_answer", "branch_operation_born", "branch_operation_equation", "branch_operation_trace", "branch_operation_faces", "branch_operation_born_whole", "branch_operation_born_next"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_operation_live_binding", "branch_operation_live_child_environment", "branch_operation_live_query", "branch_operation_live_next", "branch_operation_live_answer", "branch_operation_live_faces", "branch_operation_live_equation", "branch_operation_live_inverse", "branch_operation_live_inverse_whole", "branch_operation_live_inverse_next", "branch_operation_live_payment"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Next
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed nativeReader nativeTree)
end D
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (runtime activated_query activated_answer activated_next)
end M
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition)) (stepTargetPairingOccurrence (step root visit recognition) successor))
theorem actual_next_material : HEq
    (recognition.material.parent.commonLaw.historyAt successor.targetOccurrence)
    (recognition.material.parent.commonLaw.historyAt (root.emitted (nextVisit root visit recognition successor).current)) := by
  rw [successor_targetOccurrence_eq_emitted (step root visit recognition) successor]
  rfl


theorem current_whole_next : HEq (step root visit recognition).wholeLedgerWriteBack
    (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
    (step root visit recognition).nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨(step root visit recognition).wholeLedgerWriteBack_eq_root,
    (step root visit recognition).nextCurrent_eq_root⟩

theorem next_whole_next :
    let nextStep := recognition.generateStepAt (nextVisit root visit recognition successor)
    HEq nextStep.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (nextVisit root visit recognition successor).current) ∧
      nextStep.nextCurrent = root.generatedNextCurrentAt (nextVisit root visit recognition successor) :=
  ⟨(recognition.generateStepAt (nextVisit root visit recognition successor)).wholeLedgerWriteBack_eq_root,
    (recognition.generateStepAt (nextVisit root visit recognition successor)).nextCurrent_eq_root⟩

namespace J
export SourceOperationNative.Tree.Fold.Dependent.Joint
  (query_answer_next normal_inventory original_parent_next sourceRoot sourceVisit installedReader)
end J

theorem query_answer_next (offset : Nat) : type_of%
    (J.query_answer_next root visit recognition successor transition alignment U7 calculus offset) :=
  J.query_answer_next root visit recognition successor transition alignment U7 calculus offset

theorem parent_visit_readback (count : Nat) : type_of%
    (C.readback (J.sourceRoot root visit recognition successor transition alignment)
      (J.sourceVisit root visit recognition successor transition alignment) U7 calculus
      (J.installedReader root visit recognition successor transition alignment) count) :=
  C.readback (J.sourceRoot root visit recognition successor transition alignment)
    (J.sourceVisit root visit recognition successor transition alignment) U7 calculus
    (J.installedReader root visit recognition successor transition alignment) count

theorem temporal_normal_inverse : type_of%
    (J.normal_inventory root visit recognition successor transition alignment) :=
  J.normal_inventory root visit recognition successor transition alignment

theorem temporal_parent_next (count : Nat) : type_of%
    (J.original_parent_next root visit recognition successor transition alignment U7 calculus count) :=
  J.original_parent_next root visit recognition successor transition alignment U7 calculus count

theorem branch_query_answer_next (offset : Nat) : type_of%
    (SourceOperationNative.Tree.Fold.Dependent.Branch.query_answer_next root visit recognition U7 calculus offset) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.query_answer_next root visit recognition U7 calculus offset

theorem branch_parent_next (count : Nat) : type_of%
    (SourceOperationNative.Tree.Fold.Dependent.Branch.parent_next root visit recognition U7 calculus count) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.parent_next root visit recognition U7 calculus count

theorem branch_exact_payload (count : Nat) : type_of%
    (SourceOperationNative.Tree.Fold.Dependent.Branch.recovered_payload root visit recognition U7 calculus count) :=
  SourceOperationNative.Tree.Fold.Dependent.Branch.recovered_payload root visit recognition U7 calculus count
theorem primary_query (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_query
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_query _ _ _ _ _ _ _ _ count
theorem primary_input (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_input
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_input _ _ _ _ _ _ _ _ count
theorem primary_answer (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_answer
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_answer _ _ _ _ _ _ _ _ count
theorem primary_next (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_next
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.actual_next _ _ _ _ _ _ _ _ count
theorem primary_source_equation (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.source_equation
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.source_equation _ _ _ _ _ _ _ _ count
theorem primary_complete_query_trace (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.complete_query_trace
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.complete_query_trace _ _ _ _ _ _ _ _ count
theorem primary_four_face (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.dual_readback
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.dual_readback _ _ _ _ _ _ _ _ count
theorem primary_payment (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.macro_payment
 root visit recognition successor transition alignment U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Joint.Primary.FourFace.macro_payment _ _ _ _ _ _ _ _ count
theorem branch_primary_query (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_query
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_query _ _ _ _ _ count
theorem branch_primary_input (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_input
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_input _ _ _ _ _ count
theorem branch_primary_answer (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_answer
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_answer _ _ _ _ _ count
theorem branch_primary_next (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_next
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.actual_next _ _ _ _ _ count
theorem branch_source_equation (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.source_equation
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.source_equation _ _ _ _ _ count
theorem branch_complete_query_trace (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.complete_query_trace
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.complete_query_trace _ _ _ _ _ count
theorem branch_four_face (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.dual_readback
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.dual_readback _ _ _ _ _ count
theorem branch_primary_payment (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.macro_payment
 root visit recognition U7 calculus count) :=
 SourceOperationNative.Tree.Fold.Dependent.Branch.Primary.FourFace.macro_payment _ _ _ _ _ count
theorem branch_joint_core : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.paid_core
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.paid_core _ _ _
theorem branch_joint_relation : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.paid_relation
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.paid_relation _ _ _
theorem branch_joint_fee : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.exact_fee
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.exact_fee _ _ _
theorem branch_joint_stock : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.current_scalar_stock
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.current_scalar_stock _ _ _ _ _
theorem branch_action_environment : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.source_environment
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.source_environment _ _ _
theorem branch_action_equation : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.actual_update
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.actual_update _ _ _
theorem branch_born_environment : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Continuation.born_environment
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Continuation.born_environment _ _ _ _ _
theorem branch_source_trace : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Continuation.source_trace
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Continuation.source_trace _ _ _
theorem branch_action_paid_history : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History.actual_paid_preserved
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History.actual_paid_preserved _ _ _
theorem branch_action_full_history : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History.full_trace_preserved
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Action.History.full_trace_preserved _ _ _
theorem branch_receipt_query (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.actual_query_state
 root visit recognition U7 calculus count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.actual_query_state _ _ _ _ _ count
theorem branch_receipt_whole (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.whole_first
 root visit recognition U7 calculus count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.whole_first _ _ _ _ _ count
theorem branch_receipt_next (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.literal_next
 root visit recognition U7 calculus count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.literal_next _ _ _ _ _ count
theorem branch_receipt_inverse (count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.exact_inverse
 root visit recognition U7 calculus count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.exact_inverse _ _ _ _ _ count
theorem branch_receipt_source : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.exact_source
 root visit recognition U7 calculus 0) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.exact_source _ _ _ _ _ 0
theorem branch_receipt_visit : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.exact_visit
 root visit recognition U7 calculus 0) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.exact_visit _ _ _ _ _ 0
theorem branch_receipt_actual_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.actual_next
 root visit recognition U7 calculus 0 stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.actual_next _ _ _ _ _ 0 stage
theorem branch_receipt_preserves (stage : Nat) : type_of% ((SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.runtime
 root visit recognition U7 calculus 0).tickAt stage).next_preservesGeneratedLivingLaw :=
 ((SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.runtime root visit recognition U7 calculus 0).tickAt stage).next_preservesGeneratedLivingLaw
theorem branch_receipt_paid_stock : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.paid_trace_preserved
 root visit recognition U7 calculus 0) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.paid_trace_preserved _ _ _ _ _ 0
theorem branch_future_stock (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.stock_preserved
 root visit recognition U7 calculus 0 stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.stock_preserved _ _ _ _ _ 0 stage
theorem branch_stock_disposition (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.actual_disposition
 root visit recognition U7 calculus 0 stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.actual_disposition _ _ _ _ _ 0 stage
theorem branch_stock_equation (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.source_equation
 root visit recognition U7 calculus 0 stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.source_equation _ _ _ _ _ 0 stage
theorem branch_stock_query_trace (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.complete_query_trace
 root visit recognition U7 calculus 0 stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.complete_query_trace _ _ _ _ _ 0 stage
theorem branch_stock_four_face (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.dual_readback
 root visit recognition U7 calculus 0 stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.dual_readback _ _ _ _ _ 0 stage
theorem branch_actor_value : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.complete_initial_value
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.complete_initial_value root visit recognition
theorem branch_actor_source : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.installed_raw
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.installed_raw root visit recognition
theorem branch_actor_registered : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.registered_source
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.registered_source root visit recognition U7 calculus
theorem branch_actor_order : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.old_trace_order
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.old_trace_order root visit recognition
theorem branch_actor_stock (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.stock_preserved
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.stock_preserved root visit recognition U7 calculus stage
theorem branch_actor_disposition (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_disposition
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_disposition root visit recognition U7 calculus stage
theorem branch_actor_query (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_query
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_query root visit recognition U7 calculus stage
theorem branch_actor_input (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_input
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_input root visit recognition U7 calculus stage
theorem branch_actor_result (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_result
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_result root visit recognition U7 calculus stage
theorem branch_actor_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_next
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_next root visit recognition U7 calculus stage
theorem branch_actor_born (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_born
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.actual_born root visit recognition U7 calculus stage
theorem branch_actor_equation (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.source_equation
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.source_equation root visit recognition U7 calculus stage
theorem branch_actor_trace (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.complete_query_trace
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.complete_query_trace root visit recognition U7 calculus stage
theorem branch_actor_faces (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.four_face_dual
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.four_face_dual root visit recognition U7 calculus stage
theorem branch_actor_born_whole : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.born_whole
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.born_whole root visit recognition U7 calculus
theorem branch_actor_born_next : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.born_next
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.born_next root visit recognition U7 calculus
theorem branch_live_binding : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.initial_binding
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.initial_binding root visit recognition U7 calculus
theorem branch_live_query (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.actual_input
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.actual_input root visit recognition U7 calculus stage
theorem branch_live_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.actual_next
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.actual_next root visit recognition U7 calculus stage
theorem branch_live_answer (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.actual_answer
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.actual_answer root visit recognition U7 calculus stage
theorem branch_live_faces (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.dual_readback
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.dual_readback root visit recognition U7 calculus stage
theorem branch_live_equation (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.source_equation
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.source_equation root visit recognition U7 calculus stage
theorem branch_live_inverse (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.inverse_read
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.inverse_read root visit recognition U7 calculus stage
theorem branch_live_inverse_whole (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.inverse_whole
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.inverse_whole root visit recognition U7 calculus stage
theorem branch_live_inverse_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.inverse_next
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.inverse_next root visit recognition U7 calculus stage
theorem branch_live_payment (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.macro_payment
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.macro_payment root visit recognition U7 calculus stage
theorem branch_operation_registered : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.registered_source
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.registered_source root visit recognition U7 calculus
theorem branch_operation_source : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.installed_raw
 root visit recognition) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.installed_raw root visit recognition
theorem branch_operation_stock (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.stock_preserved
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.stock_preserved root visit recognition U7 calculus stage
theorem branch_operation_disposition (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_disposition
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_disposition root visit recognition U7 calculus stage
theorem branch_operation_query (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_query
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_query root visit recognition U7 calculus stage
theorem branch_operation_input (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_input
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_input root visit recognition U7 calculus stage
theorem branch_operation_result (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_result
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_result root visit recognition U7 calculus stage
theorem branch_operation_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_next
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_next root visit recognition U7 calculus stage
theorem branch_operation_answer (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_answer
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_answer root visit recognition U7 calculus stage
theorem branch_operation_born (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_born
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.actual_born root visit recognition U7 calculus stage
theorem branch_operation_equation (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.source_equation
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.source_equation root visit recognition U7 calculus stage
theorem branch_operation_trace (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.complete_query_trace
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.complete_query_trace root visit recognition U7 calculus stage
theorem branch_operation_faces (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.four_face_dual
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.four_face_dual root visit recognition U7 calculus stage
theorem branch_operation_born_whole : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.born_whole
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.born_whole root visit recognition U7 calculus
theorem branch_operation_born_next : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.born_next
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.born_next root visit recognition U7 calculus
theorem branch_operation_live_binding : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.initial_binding
 root visit recognition U7 calculus) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.initial_binding root visit recognition U7 calculus
theorem branch_operation_live_child_environment (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.born_child_environment root visit recognition
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.frameAt root visit recognition U7 calculus stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.sourceSeed root visit recognition U7 calculus)) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.born_child_environment root visit recognition
 (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.frameAt root visit recognition U7 calculus stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.sourceSeed root visit recognition U7 calculus)
theorem branch_operation_live_query (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.actual_input
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.actual_input root visit recognition U7 calculus stage
theorem branch_operation_live_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.actual_next
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.actual_next root visit recognition U7 calculus stage
theorem branch_operation_live_answer (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.actual_answer
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.actual_answer root visit recognition U7 calculus stage
theorem branch_operation_live_faces (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.dual_readback
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.dual_readback root visit recognition U7 calculus stage
theorem branch_operation_live_equation (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.source_equation
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.source_equation root visit recognition U7 calculus stage
theorem branch_operation_live_inverse (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.inverse_read
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.inverse_read root visit recognition U7 calculus stage
theorem branch_operation_live_inverse_whole (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.inverse_whole
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.inverse_whole root visit recognition U7 calculus stage
theorem branch_operation_live_inverse_next (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.inverse_next
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.inverse_next root visit recognition U7 calculus stage
theorem branch_operation_live_payment (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.macro_payment
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.macro_payment root visit recognition U7 calculus stage
end SourceOperationNative.Tree.Fold.Dependent.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
