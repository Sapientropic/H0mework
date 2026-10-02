import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Expression
import H0mework.Realization.ObservationActions.WordsCompletionAction

/-! The existing complete action-word model consumes the whole sealed state
before the original value and pair are read. The inverse keeps different
activations distinct even when their scalar readouts coincide. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context
open RootInquiryCompletion SourceOperationEffects SourceGeneratedActionWords
open SourceGeneratedActionObservationHistory

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)

abbrev completeRead : Carrier runtime →ₗ[ℤ] Carrier runtime := LinearMap.id

def actions (_letter : PUnit.{u + 14}) : Carrier runtime →ₗ[ℤ] Carrier runtime := sourceAction runtime

abbrev Completion := completion (sourceAction runtime) (inventory (actions runtime) (completeRead runtime))

def completionPoint (state : runtime.State) : Completion runtime :=
  sourceMap (sourceAction runtime) (inventory (actions runtime) (completeRead runtime)) (point runtime state)

def completionAction : Completion runtime →ₗ[ℤ] Completion runtime :=
  completeAdvance (actions runtime) (completeRead runtime) PUnit.unit PUnit.unit

theorem completion_point_action (state : runtime.State) :
    completionAction runtime (completionPoint runtime state) =
      completionPoint runtime state.tick.nextState := by
  exact (complete_advance_source (actions runtime) (completeRead runtime) PUnit.unit PUnit.unit
    (point runtime state)).trans
      (congrArg (sourceMap (sourceAction runtime) (inventory (actions runtime) (completeRead runtime)))
        (point_action runtime state))

def readCompletion : Completion runtime →ₗ[ℤ] Carrier runtime :=
  SourceGeneratedActionWords.completeRead (actions runtime) (completeRead runtime) PUnit.unit []

theorem read_completion_point (state : runtime.State) :
    readCompletion runtime (completionPoint runtime state) = point runtime state :=
  complete_read_source (actions runtime) (completeRead runtime) PUnit.unit [] (point runtime state)

theorem completionPoint_injective : Function.Injective (completionPoint runtime) := by
  intro first second same
  have points := congrArg (readCompletion runtime) same
  rw [read_completion_point, read_completion_point] at points
  exact Finsupp.single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0) points

theorem actual_completion_action (count : Nat) :
    completionAction runtime (completionPoint runtime (runtime.stateAt count)) =
      completionPoint runtime (runtime.stateAt (count + 1)) :=
  completion_point_action runtime (runtime.stateAt count)

end SourceOperationInquiry.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
