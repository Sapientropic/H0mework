import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Endpoint
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Effect.Consumer
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
namespace Lower.SourceFamily.Evaluated.Consumed
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (rec : RecognitionAt H root)
local instance physicalGroups : ∀ t,AddCommGroup (Act.PhysicalValue root visit rec t) := inferInstance
local instance currentGroups (n : Nat) (t : SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Slot root rec) :
 AddCommGroup (Lower.Value (Act.LowValue root visit rec) n t) := Lower.groups (Act.LowValue root visit rec) n t
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (anchor sourceStage stage count : Nat)
abbrev binding (n : Nat) := Lower.SourceFamily.Replay.Activated.bindingAt root visit rec n
abbrev seed (n : Nat) := Lower.SourceFamily.Replay.Activated.seedAt root visit rec U7 calculus anchor sourceStage stage count n
abbrev frame (n : Nat) := Lower.SourceFamily.Replay.Activated.frameAt root visit rec U7 calculus anchor sourceStage stage count n
abbrev sourceFace (n : Nat) := Lower.SourceFamily.Foresight.Contextual.Elimination.face
 (Lower.SourceFamily.Replay.Activated.OriginalBinding.lowBinding root visit rec) (n+1)
 (seed root visit rec U7 calculus anchor sourceStage stage count n)
 (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev raw (n : Nat) := (sourceFace root visit rec U7 calculus anchor sourceStage stage count n).rootRead.1.2.2.2.2.2.2.1
abbrev result (n : Nat) := (sourceFace root visit rec U7 calculus anchor sourceStage stage count n).rootRead.1.2.2.2.2.2.2.2.2.2.1

abbrev payment (n : Nat) := Lower.SourceFamily.Evaluated.active_payment (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev continuation (n : Nat) := Lower.SourceFamily.Evaluated.active_continuation (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev context (n : Nat) := Lower.SourceFamily.Evaluated.context (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev completed (n : Nat) := Lower.SourceFamily.Evaluated.completed (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev queryState (n : Nat) := Lower.SourceFamily.Evaluated.Answer.state (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev queryInput (n : Nat) := Lower.SourceFamily.Evaluated.Answer.input (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)
abbrev queryFace (n : Nat) := Lower.SourceFamily.Evaluated.Answer.face (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)

theorem actual_source_component (n : Nat) :
 raw root visit rec U7 calculus anchor sourceStage stage count n =
  Lower.SourceFamily.Evaluated.raw (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
   (frame root visit rec U7 calculus anchor sourceStage stage count n) ∧
 result root visit rec U7 calculus anchor sourceStage stage count n =
  Lower.SourceFamily.Evaluated.result (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n)
   (frame root visit rec U7 calculus anchor sourceStage stage count n) := ⟨rfl,rfl⟩

theorem actual_raw (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.raw_source (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.raw_source _ _ _

theorem actual_state (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.same_state (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.same_state _ _ _

theorem actual_source_result (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.same_result (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.same_result _ _ _

theorem actual_whole (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.whole_factorizes (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.whole_factorizes _ _ _

theorem actual_payments (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.paid_debit (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.paid_debit _ _ _

theorem actual_no_refill (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.no_refill (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.no_refill _ _ _

theorem actual_noetherian (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.noetherian (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.noetherian _ _ _

theorem actual_no_paid (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.endpoint_no_paid (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.endpoint_no_paid _ _ _

theorem actual_fee (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.complete_fee (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.complete_fee _ _ _

theorem actual_query_result (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.Answer.same_result (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.Answer.same_result _ _ _

theorem actual_terminal_value (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.Answer.terminal_value (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.Answer.terminal_value _ _ _

theorem actual_query_compilation (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.Answer.actual_compilation (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.Answer.actual_compilation _ _ _

theorem actual_query_next (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.Answer.actual_next (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.Answer.actual_next _ _ _

theorem actual_original_material (n : Nat) : type_of% (Lower.SourceFamily.Evaluated.Answer.original_material (binding root visit rec n) (seed root visit rec U7 calculus anchor sourceStage stage count n) (frame root visit rec U7 calculus anchor sourceStage stage count n)) :=
 Lower.SourceFamily.Evaluated.Answer.original_material _ _ _

theorem actual_consumption (n bound : Nat) (word : Lower.SourceFamily.Effect.Consumed.Word root visit rec n) :
 type_of% (actual_source_component root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_raw root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_state root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_source_result root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_whole root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_payments root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_no_refill root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_noetherian root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_no_paid root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_fee root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_query_result root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_terminal_value root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_query_compilation root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_query_next root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (actual_original_material root visit rec U7 calculus anchor sourceStage stage count n) ∧
 type_of% (Lower.SourceFamily.Effect.Consumed.actual_consumption root visit rec U7 calculus anchor sourceStage stage count n bound word) :=
 ⟨actual_source_component _ _ _ _ _ _ _ _ _ n,actual_raw _ _ _ _ _ _ _ _ _ n,
 actual_state _ _ _ _ _ _ _ _ _ n,
 actual_source_result _ _ _ _ _ _ _ _ _ n,
 actual_whole _ _ _ _ _ _ _ _ _ n,
 actual_payments _ _ _ _ _ _ _ _ _ n,
 actual_no_refill _ _ _ _ _ _ _ _ _ n,
 actual_noetherian _ _ _ _ _ _ _ _ _ n,
 actual_no_paid _ _ _ _ _ _ _ _ _ n,
 actual_fee _ _ _ _ _ _ _ _ _ n,
 actual_query_result _ _ _ _ _ _ _ _ _ n,
 actual_terminal_value _ _ _ _ _ _ _ _ _ n,
 actual_query_compilation _ _ _ _ _ _ _ _ _ n,
 actual_query_next _ _ _ _ _ _ _ _ _ n,
 actual_original_material _ _ _ _ _ _ _ _ _ n,
 Lower.SourceFamily.Effect.Consumed.actual_consumption _ _ _ _ _ _ _ _ _ n bound word⟩
end Lower.SourceFamily.Evaluated.Consumed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
