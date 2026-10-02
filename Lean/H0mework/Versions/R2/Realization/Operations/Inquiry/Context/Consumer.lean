import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Action

/-! The generated pair trace and its complete relation fibre are consumed
with the original tick's typed receipt and exact heterogeneous successor. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarInventoryLift SourceOperationScalarPresentation

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

/-- This read applies the existing complete model inverse before projecting
the original environment. It cannot decode an arbitrary word as a state. -/
def completionEnvironment (value : Completion runtime) : Env PhysicalValue PhysicalVar :=
  environment runtime source (readCompletion runtime value)

theorem actual_next_environment (state : runtime.State) :
    completionEnvironment runtime source (completionAction runtime (completionPoint runtime state)) =
      readEnv runtime source state.tick.nextState := by
  rw [completionEnvironment, completion_point_action, read_completion_point, environment_point]

theorem actual_operation_receipt (state : runtime.State) :
    (pairTrace runtime source state).length = remaining (liftExpr (raw runtime source state).expression) ∧
    (raw runtime source state).expression.eval
      (completionEnvironment runtime source (completionAction runtime (completionPoint runtime state))) =
        (pairValue runtime source state).1 + (pairValue runtime source state).2 ∧
    HEq state.tick.receipt (state.engine.ask state.activation).receipt ∧
    state.tick.nextState.engine.node.erase = (state.engine.ask state.activation).next.node.erase ∧
    state.engine.node.PreservesGeneratedLivingLawAt state.activation.query state.tick.nextState.engine.node := by
  exact ⟨pair_trace_length runtime source state, by rw [actual_next_environment]; exact next_value runtime source state,
    HEq.rfl, rfl, state.tick.next_preservesGeneratedLivingLaw⟩

theorem inventory_fibre (state : runtime.State)
    (left right : Formal ℤ PhysicalValue PhysicalVar sort) :
    updateInventory (R := ℤ) (readEnv runtime source state) (increment runtime source state) left =
        updateInventory (R := ℤ) (readEnv runtime source state) (increment runtime source state) right ↔
      liftMap (R := ℤ) (left - right) ∈ LinearMap.range (relationMap (R := ℤ)
        (pairEnvironmentAt runtime source state)) :=
  inventory_fibre_generated _ _ _ _

theorem completion_same_typed (first second : runtime.State)
    (same : completionPoint runtime first = completionPoint runtime second) :
    HEq first.activation.query second.activation.query ∧
    HEq first.activation.origin second.activation.origin ∧
    HEq first.tick.resolution second.tick.resolution ∧ HEq first.tick.receipt second.tick.receipt := by
  have states := completionPoint_injective runtime same
  cases states
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem actual_operation (count : Nat) :
    completionEnvironment runtime source (completionAction runtime (completionPoint runtime (runtime.stateAt count))) =
      readEnv runtime source (runtime.stateAt (count + 1)) ∧
    HEq (runtime.tickAt count).receipt
      ((runtime.stateAt count).engine.ask (runtime.stateAt count).activation).receipt ∧
    (runtime.stateAt (count + 1)).engine.node.erase =
      ((runtime.stateAt count).engine.ask (runtime.stateAt count).activation).next.node.erase :=
  ⟨actual_next_environment runtime source (runtime.stateAt count), HEq.rfl, rfl⟩

theorem zero_not_completionPoint (state : runtime.State) : (0 : Completion runtime) ≠ completionPoint runtime state := by
  intro same
  have points := congrArg (readCompletion runtime) same
  rw [map_zero, read_completion_point] at points
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (Finsupp.single_eq_zero.mp points.symm)

end SourceOperationInquiry.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
