import H0mework.Versions.R2.Realization.Operations.Inquiry.Source

/-! Complete field equality retains the source query, activation and typed
receipt. The field action follows the very same heterogeneous macro tick. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry
open RootInquiryCompletion

noncomputable section
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)

theorem typed_data_of_field_eq (first second : runtime.State)
    (same : fieldPoint runtime first = fieldPoint runtime second) :
    HEq first.activation.query second.activation.query ∧
    HEq first.activation.origin second.activation.origin ∧
    HEq first.tick.resolution second.tick.resolution ∧
    HEq first.tick.receipt second.tick.receipt := by
  have states := fieldPoint_injective runtime same
  cases states
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem actual_factorizes (state : runtime.State) :
    word runtime (fieldPoint runtime state) = point runtime state ∧
    fieldAction runtime (fieldPoint runtime state) = fieldPoint runtime state.tick.nextState ∧
    state.tick.resolution = (state.engine.ask state.activation).resolution ∧
    HEq state.tick.receipt (state.engine.ask state.activation).receipt ∧
    state.tick.nextState.engine.node.erase = (state.engine.ask state.activation).next.node.erase ∧
    state.engine.node.PreservesGeneratedLivingLawAt state.activation.query state.tick.nextState.engine.node :=
  ⟨word_point runtime state, field_action runtime state, rfl,
    HEq.rfl, rfl, state.tick.next_preservesGeneratedLivingLaw⟩

theorem actual_next_word (count : Nat) :
    word runtime (fieldAction runtime (fieldPoint runtime (runtime.stateAt count))) =
      point runtime (runtime.stateAt (count + 1)) :=
  (congrArg (word runtime) (actual_field_action runtime count)).trans
    (word_point runtime (runtime.stateAt (count + 1)))

theorem actual_next_receipt (count : Nat) :
    HEq (runtime.tickAt count).receipt
      ((runtime.stateAt count).engine.ask (runtime.stateAt count).activation).receipt ∧
    (runtime.stateAt (count + 1)).engine.node.erase =
      ((runtime.stateAt count).engine.ask (runtime.stateAt count).activation).next.node.erase ∧
    (runtime.stateAt count).engine.node.PreservesGeneratedLivingLawAt
      (runtime.stateAt count).activation.query (runtime.stateAt (count + 1)).engine.node :=
  ⟨HEq.rfl, rfl,
    (runtime.tickAt count).next_preservesGeneratedLivingLaw⟩

theorem zero_not_native (state : runtime.State) : (0 : Field runtime) ≠ fieldPoint runtime state :=
  SourceOwnedObservationHistory.FullWord.zero_not_native (nextState runtime) state

end
end SourceOperationInquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
