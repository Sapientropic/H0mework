import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Reverse.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Consumer

/-! The existing word executor consumes the source-generated reverse fibre,
its complete coefficient syntax and original whole write, trace and next. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Reverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationLogic
open SourceOperationLogic.FibreLift SourceGeneratedScalarDifferentialResidual
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)
variable (state : runtime.State)

theorem reverse_pair : recover runtime source state (reverse runtime source state) =
    ((raw runtime source state).expression.eval (readEnv runtime source state) -
       (raw runtime source state).expression.eval (readEnv runtime source state.tick.nextState),
     (raw runtime source state).expression.effect (readEnv runtime source state)
       (increment runtime source state)) := by
  rw [reverse_recover, source_boundary]
  apply Prod.ext
  · simp only [pairInventory, updateInventory, LinearMap.prod_apply, Function.prod,
      map_sub, evaluation, Finsupp.linearCombination_single, one_smul, Expr.eval, Prod.fst_sub]
  · simp only [pairInventory, updateInventory, LinearMap.prod_apply, Function.prod,
      map_sub, effectEvaluator, Finsupp.linearCombination_single, one_smul, Expr.effect,
      Prod.snd_sub, sub_zero]

theorem source_execution : Execution.value runtime source state (nextWord runtime source state) =
    recover runtime source state (reverse runtime source state) := by
  have generated := Execution.value_recovered runtime source state
    (oldWord runtime source state) (target runtime source state)
  simpa only [target, reverse, add_sub_cancel_left] using generated

theorem source_write : type_of% (Execution.actual_whole runtime source state (nextWord runtime source state)) :=
  Execution.actual_whole runtime source state (nextWord runtime source state)

theorem source_trace : type_of% (Execution.trace_cost runtime source state (nextWord runtime source state)) :=
  Execution.trace_cost runtime source state (nextWord runtime source state)

theorem source_original : type_of% (Execution.original_occurrence runtime source state (nextWord runtime source state)) :=
  Execution.original_occurrence runtime source state (nextWord runtime source state)

theorem source_next : type_of% (Execution.actual_tick runtime source state (nextWord runtime source state)) :=
  Execution.actual_tick runtime source state (nextWord runtime source state)

theorem actual_tick : HEq state.tick.receipt (state.engine.ask state.activation).receipt ∧
    state.tick.nextState.engine.node.erase = (state.engine.ask state.activation).next.node.erase ∧
    state.engine.node.PreservesGeneratedLivingLawAt state.activation.query state.tick.nextState.engine.node :=
  ⟨HEq.rfl, rfl, state.tick.next_preservesGeneratedLivingLaw⟩

end SourceOperationInquiry.Context.Faces.Reverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
