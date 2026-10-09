import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Written
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Phase.Effect
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Phase.Closed
section Generic
variable {S : Type u} {U X : S → Type u} [∀ t, AddCommGroup (U t)] {s : S}

private theorem evaluation_single_unit (environment : Env U X) (expression : Expr U X s) :
    evaluation (R:=ℤ) environment (Finsupp.single expression 1) = expression.eval environment := by
  rw [evaluation, Finsupp.linearCombination_single, one_smul]

variable {environment : Env U X} {before after : Expr U X s}
private theorem exposed_word (trace : Trace environment before after)
    (word : Formal ℤ U X s) (present : word ∈ SourceOperationPaidRelations.words trace) :
    PresentedRelationEventAt.relation word ∈ (SourceOperationPaidRelations.exposure trace).trace := by
  change PresentedRelationEventAt.relation word ∈ PresentedRelationEventAt.generator before ::
    RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events trace)
  apply List.mem_cons_of_mem
  rw [SourceOperationPaidRelations.events_trace]
  exact List.mem_map_of_mem present

private theorem list_sum_mem (module : Submodule ℤ (Formal ℤ U X s))
    (items : List (Formal ℤ U X s))
    (present : ∀ item ∈ items, item ∈ module) : items.sum ∈ module := by
  induction items with
  | nil => exact module.zero_mem
  | cons item rest previous =>
    exact module.add_mem (present item List.mem_cons_self)
      (previous (fun later member => present later (List.mem_cons_of_mem _ member)))

private theorem paid_boundary_mem (module : Submodule ℤ (Formal ℤ U X s))
    (trace : Trace environment before after)
    (present : ∀ word ∈ SourceOperationPaidRelations.words trace, word ∈ module) :
    relationMap (R:=ℤ) environment (trace.relationWords (R:=ℤ)) ∈ module :=
  (SourceOperationPaidRelations.paid_boundary trace) ▸
    list_sum_mem module (SourceOperationPaidRelations.words trace) present
end Generic

variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding : ∀ t, X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

abbrev history := Lower.SourceFamily.Foresight.Contextual.Written.jointHistory binding n data
abbrev face := Lower.SourceFamily.Foresight.Contextual.Effect.jointFace binding n data
abbrev requestExpression := Lower.SourceFamily.Foresight.Contextual.Phase.requestExpression binding n data
abbrev requestTrace := Lower.SourceFamily.Foresight.Contextual.Phase.requestTrace binding n data
abbrev requestWritten := Lower.SourceFamily.Foresight.Contextual.Phase.requestWritten binding n data

private theorem written_observed (event) (present : event ∈ (requestWritten binding n data).trace) :
    event ∈ (history binding n data).observedEvents 0 := by
  have actual := Lower.SourceFamily.Foresight.Contextual.Phase.complete_paid_in_history
    binding n data event present
  simpa only [RootGeneratedCofinalHistoryAt.observedEvents, List.range_succ,
    List.range_zero, List.nil_append, List.flatMap_singleton] using actual

theorem request_generator_closure :
    Finsupp.single (requestExpression binding n data) (1 : ℤ) ∈
      (history binding n data).generatorClosure := by
  classical
  have actual := written_observed binding n data
    (.generator (requestExpression binding n data)) List.mem_cons_self
  have support : requestExpression binding n data ∈ (history binding n data).generatorSupport 0 := by
    rw [RootGeneratedCofinalHistoryAt.generatorSupport, List.mem_toFinset, List.mem_flatMap]
    exact ⟨.generator (requestExpression binding n data), actual,
      by simp only [PresentedRelationEventAt.support, Finset.toList_singleton, List.mem_singleton]⟩
  exact (history binding n data).generatorStage_le_closure 0
    (Finsupp.single_mem_supported ℤ 1 support)

def requestVector : (history binding n data).generatorClosure :=
  ⟨Finsupp.single (requestExpression binding n data) 1, request_generator_closure binding n data⟩

theorem closure_value : (face binding n data).closureEvaluation (requestVector binding n data) =
    (Lower.SourceFamily.Foresight.Paid.result binding n data s
      (Lower.SourceFamily.Foresight.Contextual.Phase.requestWord binding n data)).2.2.1 := by
  change (face binding n data).freeEvaluation (Finsupp.single (requestExpression binding n data) 1) = _
  have source : (Lower.SourceFamily.Foresight.Paid.result binding n data s
      (Lower.SourceFamily.Foresight.Contextual.Phase.requestWord binding n data)).2.2.1 =
      (requestExpression binding n data).eval (Lower.SourceFamily.Foresight.Paid.sourceEnv binding n data) :=
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
  exact (Lower.SourceFamily.Foresight.Contextual.Effect.joint_word_read binding n data _).trans
    ((evaluation_single_unit _ (requestExpression binding n data)).trans
      (source.trans (congrArg (fun environment => (requestExpression binding n data).eval environment)
        (Lower.SourceFamily.Foresight.Contextual.Effect.source_environment binding n data))).symm)

theorem generated_two_channel_value : type_of%
 ((closure_value binding n data).trans (Lower.SourceFamily.Foresight.Contextual.Phase.paid_pair binding n data)) :=
 (closure_value binding n data).trans (Lower.SourceFamily.Foresight.Contextual.Phase.paid_pair binding n data)

variable (word : Formal ℤ (PairValue (Lower.Value W (n+1))) X s)
variable (exposed : PresentedRelationEventAt.relation word ∈ (requestWritten binding n data).trace)
include exposed

theorem relation_closure : word ∈ (history binding n data).relationClosure :=
  (history binding n data).relationStage_le_closure 0
    (Submodule.subset_span (written_observed binding n data (.relation word) exposed))

theorem relation_next_kernel : (face binding n data).freeEvaluation word = 0 := by
  have source : evaluation (R:=ℤ) (Lower.SourceFamily.Foresight.Paid.sourceEnv binding n data) word = 0 :=
    SourceOperationPaidRelations.exposure_sound (requestTrace binding n data) word exposed
  exact (Lower.SourceFamily.Foresight.Contextual.Effect.joint_word_read binding n data word).trans
    ((congrArg (fun environment => evaluation (R:=ℤ) environment word)
      (Lower.SourceFamily.Foresight.Contextual.Effect.source_environment binding n data).symm).trans source)

theorem relation_consumer : word ∈ (history binding n data).relationClosure ∧
    (face binding n data).freeEvaluation word = 0 :=
  ⟨relation_closure binding n data word exposed, relation_next_kernel binding n data word exposed⟩

omit exposed in
theorem paid_word_exposed (present : word ∈ SourceOperationPaidRelations.words (requestTrace binding n data)) :
    PresentedRelationEventAt.relation word ∈ (requestWritten binding n data).trace :=
  exposed_word (requestTrace binding n data) word present

def boundary := relationMap (R:=ℤ) (Lower.SourceFamily.Foresight.Paid.sourceEnv binding n data)
  ((requestTrace binding n data).relationWords (R:=ℤ))

omit word exposed in
theorem boundary_closure : boundary binding n data ∈ (history binding n data).relationClosure :=
  paid_boundary_mem (history binding n data).relationClosure (requestTrace binding n data) (fun paid present =>
    relation_closure binding n data paid (paid_word_exposed binding n data paid present))

omit word exposed in
theorem boundary_consumer : boundary binding n data ∈ (history binding n data).relationClosure ∧
    (face binding n data).freeEvaluation (boundary binding n data) = 0 :=
  ⟨boundary_closure binding n data,
    Lower.SourceFamily.Foresight.Contextual.Effect.joint_new_kernel binding n data
      (Lower.SourceFamily.Foresight.Contextual.Phase.requestWord binding n data)⟩

end Lower.SourceFamily.Foresight.Contextual.Phase.Closed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
