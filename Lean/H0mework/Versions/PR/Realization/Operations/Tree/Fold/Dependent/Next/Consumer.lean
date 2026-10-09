import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Live.FourFace.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Installation.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Next.Source
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.Primary.FourFace
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Primary.FourFace
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.PrimaryConsumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Next.PursuitConsumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.Effect
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.RichConsumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Continuation.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Receipt.Born.Stock.FourFace.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Installation.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.Consumer
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Live.FourFace.Consumer
import Lean.LibrarySuggestions.Basic
-- Large dependent runtime mouths are used directly by their consumers.
run_cmd Lean.modifyEnv fun env => ["branch_actor_value", "branch_actor_source", "branch_actor_registered", "branch_actor_order", "branch_actor_stock", "branch_actor_disposition", "branch_actor_query", "branch_actor_input", "branch_actor_result", "branch_actor_next", "branch_actor_born", "branch_actor_equation", "branch_actor_trace", "branch_actor_faces", "branch_actor_born_whole", "branch_actor_born_next"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_live_binding", "branch_live_query", "branch_live_next", "branch_live_answer", "branch_live_faces", "branch_live_equation", "branch_live_inverse", "branch_live_inverse_whole", "branch_live_inverse_next", "branch_live_payment"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_operation_registered", "branch_operation_source", "branch_operation_stock", "branch_operation_disposition", "branch_operation_query", "branch_operation_input", "branch_operation_result", "branch_operation_next", "branch_operation_answer", "branch_operation_born", "branch_operation_equation", "branch_operation_trace", "branch_operation_faces", "branch_operation_born_whole", "branch_operation_born_next"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_operation_live_binding", "branch_operation_live_child_environment", "branch_operation_live_query", "branch_operation_live_next", "branch_operation_live_answer", "branch_operation_live_faces", "branch_operation_live_equation", "branch_operation_live_inverse", "branch_operation_live_inverse_whole", "branch_operation_live_inverse_next", "branch_operation_live_payment"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_observer_occurrence", "branch_observer_observation", "branch_observer_gram", "branch_observer_stock", "branch_observer_query", "branch_observer_next", "branch_observer_faces", "branch_observer_fibre", "branch_observer_cofinal", "branch_observer_equation", "branch_observer_inverse_whole", "branch_observer_inverse_next", "branch_observer_payment", "branch_observer_noetherian"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_observer_live_query", "branch_observer_live_next", "branch_observer_live_answer", "branch_observer_live_payment", "branch_observer_live_inverse_whole", "branch_observer_live_inverse_next", "branch_observer_live_noetherian", "branch_observer_live_faces", "branch_observer_live_equation", "branch_observer_live_relation", "branch_observer_live_binding", "branch_observer_live_write", "branch_observer_live_kernel", "branch_observer_live_prior", "branch_observer_live_paid_next"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_observer_active_environment", "branch_observer_active_future", "branch_observer_active_future_next", "branch_observer_active_observation", "branch_observer_active_observation_effect", "branch_observer_active_gram", "branch_observer_active_gram_effect", "branch_observer_active_fibre", "branch_observer_active_recover", "branch_observer_active_reverse", "branch_observer_active_whole", "branch_observer_active_next", "branch_observer_active_trace"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_current_child_old_output", "branch_current_child_occurrence", "branch_current_child_actor", "branch_current_child_observation", "branch_current_child_gram", "branch_current_child_stock", "branch_current_child_query", "branch_current_child_next", "branch_current_child_faces", "branch_current_child_fibre", "branch_current_child_cofinal", "branch_current_child_equation", "branch_current_child_inverse_whole", "branch_current_child_inverse_next", "branch_current_child_payment", "branch_current_child_noetherian"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_current_dynamic_child", "branch_current_dynamic_next_child", "branch_current_dynamic_input", "branch_current_dynamic_next", "branch_current_dynamic_answer", "branch_current_dynamic_inverse_whole", "branch_current_dynamic_inverse_next", "branch_current_dynamic_payment", "branch_current_dynamic_noetherian", "branch_current_dynamic_origin", "branch_current_dynamic_word", "branch_current_dynamic_support", "branch_current_dynamic_catalogue", "branch_current_dynamic_next_word", "branch_current_dynamic_next_support", "branch_current_dynamic_observation", "branch_current_dynamic_gram", "branch_current_dynamic_next_observation", "branch_current_dynamic_next_gram", "branch_current_dynamic_faces", "branch_current_dynamic_equation", "branch_current_dynamic_relation", "branch_current_dynamic_low_stock", "branch_current_dynamic_low_disposition", "branch_current_dynamic_low_query", "branch_current_dynamic_low_next", "branch_current_dynamic_low_faces", "branch_current_dynamic_low_noetherian"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_current_main_raw", "branch_current_main_environment", "branch_current_main_syntax", "branch_current_main_increment", "branch_current_main_result", "branch_current_main_future", "branch_current_main_fibre", "branch_current_main_reverse", "branch_current_main_boundary", "branch_current_main_recover", "branch_current_main_whole", "branch_current_main_trace", "branch_current_main_original", "branch_current_main_next", "branch_current_main_tick", "branch_current_main_delta", "branch_current_main_correction", "branch_current_main_equation", "branch_current_main_correction_addition", "branch_current_main_correction_whole", "branch_current_main_correction_trace", "branch_current_main_correction_next", "branch_current_main_successor_boundary"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

run_cmd Lean.modifyEnv fun env => ["branch_outgoing_target_current", "branch_outgoing_target_old", "branch_outgoing_target_registered", "branch_outgoing_target_packet", "branch_outgoing_target_environment", "branch_outgoing_all_old_projection", "branch_outgoing_current_raw", "branch_outgoing_next_raw", "branch_outgoing_delta_word", "branch_outgoing_source_equation", "branch_outgoing_source_correction", "branch_outgoing_source_pair_addition", "branch_outgoing_scalar_fee", "branch_outgoing_pair_fee", "branch_outgoing_next_syntax_fee", "branch_outgoing_initial_pair", "branch_outgoing_written_preserved", "branch_outgoing_outgoing_scalar_preserved", "branch_outgoing_delta_scalar_preserved", "branch_outgoing_next_syntax_preserved", "branch_outgoing_outgoing_pair_preserved"].foldl Lean.LibrarySuggestions.nameDenyListExt.addEntry env

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
theorem branch_current_dynamic_child (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.current_child
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.current_child _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_next_child (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.next_child
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.next_child _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_input (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.actual_input
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.actual_input _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_next (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.actual_next
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.actual_next _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_answer (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.actual_answer
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.actual_answer _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_inverse_whole (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.inverse_whole
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.inverse_whole _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_inverse_next (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.inverse_next
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.inverse_next _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_payment (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.macro_payment
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.macro_payment _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_noetherian (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.noetherian
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.noetherian _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_origin (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin.uniform_origin
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin.uniform_origin _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_word (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.current_word
 root visit recognition U7 calculus anchor sourceStage stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.current_word _ _ _ _ _ _ _ stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))
theorem branch_current_dynamic_support (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.current_support
 root visit recognition U7 calculus anchor sourceStage stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.current_support _ _ _ _ _ _ _ stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))
theorem branch_current_dynamic_catalogue (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.current_catalogue
 root visit recognition U7 calculus anchor sourceStage stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.current_catalogue _ _ _ _ _ _ _ stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))
theorem branch_current_dynamic_next_word (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.next_word
 root visit recognition U7 calculus anchor sourceStage stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.next_word _ _ _ _ _ _ _ stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))
theorem branch_current_dynamic_next_support (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.next_support
 root visit recognition U7 calculus anchor sourceStage stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Selected.next_support _ _ _ _ _ _ _ stage (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.E.Shared.actualOccurrence (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.frameAt root visit recognition U7 calculus anchor sourceStage stage))
theorem branch_current_dynamic_observation (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.current_observation
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.current_observation _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_gram (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.current_gram
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.current_gram _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_next_observation (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.next_observation
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.next_observation _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_next_gram (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.next_gram
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Physical.next_gram _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_faces (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.dual_readback
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.dual_readback _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_equation (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.source_equation
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.source_equation _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_relation (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.actual_relation
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.FourFace.actual_relation _ _ _ _ _ _ _ stage
theorem branch_current_dynamic_low_stock (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.stock_preserved
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.stock_preserved _ _ _ _ _ _ _ _ offset
theorem branch_current_dynamic_low_disposition (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.actual_disposition
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.actual_disposition _ _ _ _ _ _ _ _ offset
theorem branch_current_dynamic_low_query (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.actual_query
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.actual_query _ _ _ _ _ _ _ _ offset
theorem branch_current_dynamic_low_next (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.actual_next
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.actual_next _ _ _ _ _ _ _ _ offset
theorem branch_current_dynamic_low_faces (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.four_faces
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.four_faces _ _ _ _ _ _ _ _ offset
theorem branch_current_dynamic_low_noetherian (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.noetherian
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.noetherian _ _ _ _ _ _ _ _ offset
theorem branch_current_child_old_output (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_old_output
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_old_output _ _ _ _ _ _ _
theorem branch_current_child_occurrence (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.exact_occurrence
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.exact_occurrence _ _ _ _ _ _ _
theorem branch_current_child_actor (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_actor
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_actor _ _ _ _ _ _ _
theorem branch_current_child_observation (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_observation
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_observation _ _ _ _ _ _ _
theorem branch_current_child_gram (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_gram
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.registered_gram _ _ _ _ _ _ _
theorem branch_current_child_stock (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.stock_preserved
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.stock_preserved _ _ _ _ _ _ _ offset
theorem branch_current_child_query (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.actual_input
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.actual_input _ _ _ _ _ _ _ offset
theorem branch_current_child_next (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.actual_next
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.actual_next _ _ _ _ _ _ _ offset
theorem branch_current_child_faces (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.four_faces
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.four_faces _ _ _ _ _ _ _ offset
theorem branch_current_child_fibre (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.complete_fibre
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.complete_fibre _ _ _ _ _ _ _ offset
theorem branch_current_child_cofinal (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.cofinal_next
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.cofinal_next _ _ _ _ _ _ _ offset
theorem branch_current_child_equation (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.source_equation
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.source_equation _ _ _ _ _ _ _ offset
theorem branch_current_child_inverse_whole (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.inverse_whole
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.inverse_whole _ _ _ _ _ _ _ offset
theorem branch_current_child_inverse_next (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.inverse_next
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.inverse_next _ _ _ _ _ _ _ offset
theorem branch_current_child_payment (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.macro_payment
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.macro_payment _ _ _ _ _ _ _ offset
theorem branch_current_child_noetherian (anchor stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.noetherian
 root visit recognition U7 calculus anchor stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Installation.noetherian _ _ _ _ _ _ _ offset
theorem branch_observer_occurrence (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.exact_occurrence
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.exact_occurrence root visit recognition U7 calculus stage
theorem branch_observer_observation (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.registered_observation
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.registered_observation root visit recognition U7 calculus stage
theorem branch_observer_gram (stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.registered_gram
 root visit recognition U7 calculus stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.registered_gram root visit recognition U7 calculus stage
theorem branch_observer_stock (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.stock_preserved
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.stock_preserved root visit recognition U7 calculus stage offset
theorem branch_observer_query (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.actual_input
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.actual_input root visit recognition U7 calculus stage offset
theorem branch_observer_next (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.actual_next
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.actual_next root visit recognition U7 calculus stage offset
theorem branch_observer_faces (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.four_faces
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.four_faces root visit recognition U7 calculus stage offset
theorem branch_observer_fibre (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.complete_fibre
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.complete_fibre root visit recognition U7 calculus stage offset
theorem branch_observer_cofinal (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.cofinal_next
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.cofinal_next root visit recognition U7 calculus stage offset
theorem branch_observer_equation (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.source_equation
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.source_equation root visit recognition U7 calculus stage offset
theorem branch_observer_inverse_whole (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.inverse_whole
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.inverse_whole root visit recognition U7 calculus stage offset
theorem branch_observer_inverse_next (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.inverse_next
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.inverse_next root visit recognition U7 calculus stage offset
theorem branch_observer_payment (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.macro_payment
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.macro_payment root visit recognition U7 calculus stage offset
theorem branch_observer_noetherian (stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.noetherian
 root visit recognition U7 calculus stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Installation.noetherian root visit recognition U7 calculus stage offset
theorem branch_observer_live_query (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.actual_input
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.actual_input root visit recognition U7 calculus anchor stage
theorem branch_observer_live_next (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.actual_next
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.actual_next root visit recognition U7 calculus anchor stage
theorem branch_observer_live_answer (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.actual_answer
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.actual_answer root visit recognition U7 calculus anchor stage
theorem branch_observer_live_payment (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.macro_payment
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.macro_payment root visit recognition U7 calculus anchor stage
theorem branch_observer_live_inverse_whole (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.inverse_whole
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.inverse_whole root visit recognition U7 calculus anchor stage
theorem branch_observer_live_inverse_next (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.inverse_next
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.inverse_next root visit recognition U7 calculus anchor stage
theorem branch_observer_live_noetherian (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.noetherian
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.noetherian root visit recognition U7 calculus anchor stage
theorem branch_observer_live_faces (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.dual_readback
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.dual_readback root visit recognition U7 calculus anchor stage
theorem branch_observer_live_equation (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.source_equation
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.source_equation root visit recognition U7 calculus anchor stage
theorem branch_observer_live_relation (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.actual_relation
 root visit recognition U7 calculus anchor stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.FourFace.actual_relation root visit recognition U7 calculus anchor stage
theorem branch_observer_live_binding (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.born_child_environment
 root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.born_child_environment root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)
theorem branch_observer_live_write (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.action_preserved
 root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.action_preserved root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)
theorem branch_observer_live_kernel (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.original_scalar_write
 root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.original_scalar_write root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)
theorem branch_observer_live_prior (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.prior_next
 root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.prior_next root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)
theorem branch_observer_live_paid_next (anchor stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.new_paid_next
 root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.new_paid_next root visit recognition U7 calculus anchor (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.frameAt root visit recognition U7 calculus anchor stage) (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.Live.sourceSeed root visit recognition U7 calculus anchor)
theorem branch_observer_active_environment (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.environment_actual
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.environment_actual root visit recognition U7 calculus anchor
theorem branch_observer_active_future (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_pair
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_pair root visit recognition U7 calculus anchor
theorem branch_observer_active_future_next (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_pair_next
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_pair_next root visit recognition U7 calculus anchor
theorem branch_observer_active_observation (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_observation_old
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_observation_old root visit recognition U7 calculus anchor
theorem branch_observer_active_observation_effect (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_observation_effect
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_observation_effect root visit recognition U7 calculus anchor
theorem branch_observer_active_gram (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_gram_old
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_gram_old root visit recognition U7 calculus anchor
theorem branch_observer_active_gram_effect (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_gram_effect
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.future_gram_effect root visit recognition U7 calculus anchor
theorem branch_observer_active_fibre (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.complete_fibre
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.complete_fibre root visit recognition U7 calculus anchor
theorem branch_observer_active_recover (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.residual_recover_injective
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.residual_recover_injective root visit recognition U7 calculus anchor
theorem branch_observer_active_reverse (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_reverse_pair
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_reverse_pair root visit recognition U7 calculus anchor
theorem branch_observer_active_whole (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_whole
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_whole root visit recognition U7 calculus anchor
theorem branch_observer_active_next (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_next
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_next root visit recognition U7 calculus anchor
theorem branch_observer_active_trace (anchor : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_trace
 root visit recognition U7 calculus anchor) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.ActiveRaw.source_trace root visit recognition U7 calculus anchor

theorem branch_current_main_raw (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.raw_actual
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.raw_actual root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_environment (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.environment_actual
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.environment_actual root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_syntax (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.syntax_actual
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.syntax_actual root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_increment (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.increment_actual
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.increment_actual root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_result (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.main_result_value
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.main_result_value root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_future (anchor sourceStage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.all_words_future
 root visit recognition U7 calculus anchor sourceStage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.all_words_future root visit recognition U7 calculus anchor sourceStage
theorem branch_current_main_fibre (anchor sourceStage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.complete_fibre_generated
 root visit recognition U7 calculus anchor sourceStage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.complete_fibre_generated root visit recognition U7 calculus anchor sourceStage
theorem branch_current_main_reverse (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.reverse_pair
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.reverse_pair root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_boundary (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.reverse_boundary
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.reverse_boundary root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_recover (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.residual_recover_injective
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.residual_recover_injective root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_whole (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_whole
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_whole root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_trace (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_trace
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_trace root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_original (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_original
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_original root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_next (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_next
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.source_next root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_tick (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.main_tick_receipt
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.main_tick_receipt root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_delta (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.syntax_delta_actual
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.syntax_delta_actual root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_correction (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_actual
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_actual root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_equation (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.actual_paid_equation
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.actual_paid_equation root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_correction_addition (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_addition
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_addition root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_correction_whole (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_whole
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_whole root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_correction_trace (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_trace
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_trace root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_correction_next (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_next
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.correction_next root visit recognition U7 calculus anchor sourceStage count
theorem branch_current_main_successor_boundary (anchor sourceStage count : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.successor_boundary
 root visit recognition U7 calculus anchor sourceStage count) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.MainRaw.Moving.successor_boundary root visit recognition U7 calculus anchor sourceStage count

theorem branch_outgoing_target_current (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_current
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_current root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_target_old (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_old
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_old root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_target_registered (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_registered
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_registered root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_target_packet (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_packet
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_packet root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_target_environment (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_environment
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.target_environment root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_all_old_projection (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.all_old_projection
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.all_old_projection root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_current_raw (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.current_raw
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.current_raw root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_next_raw (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.next_raw
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.next_raw root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_delta_word (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.delta_word
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.delta_word root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_source_equation (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.source_equation
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.source_equation root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_source_correction (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.source_correction
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.source_correction root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_source_pair_addition (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.source_pair_addition
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.source_pair_addition root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_scalar_fee (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.scalar_fee
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.scalar_fee root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_pair_fee (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.pair_fee
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.pair_fee root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_next_syntax_fee (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.next_syntax_fee
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Admission.next_syntax_fee root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_initial_pair (anchor sourceStage stage : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.initial_pair
 root visit recognition U7 calculus anchor sourceStage stage) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.initial_pair root visit recognition U7 calculus anchor sourceStage stage
theorem branch_outgoing_written_preserved (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.written_preserved
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.written_preserved root visit recognition U7 calculus anchor sourceStage stage offset
theorem branch_outgoing_outgoing_scalar_preserved (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.outgoing_scalar_preserved
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.outgoing_scalar_preserved root visit recognition U7 calculus anchor sourceStage stage offset
theorem branch_outgoing_delta_scalar_preserved (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.delta_scalar_preserved
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.delta_scalar_preserved root visit recognition U7 calculus anchor sourceStage stage offset
theorem branch_outgoing_next_syntax_preserved (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.next_syntax_preserved
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.next_syntax_preserved root visit recognition U7 calculus anchor sourceStage stage offset
theorem branch_outgoing_outgoing_pair_preserved (anchor sourceStage stage offset : Nat) : type_of% (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.outgoing_pair_preserved
 root visit recognition U7 calculus anchor sourceStage stage offset) := SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.LowStock.outgoing_pair_preserved root visit recognition U7 calculus anchor sourceStage stage offset
end SourceOperationNative.Tree.Fold.Dependent.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
