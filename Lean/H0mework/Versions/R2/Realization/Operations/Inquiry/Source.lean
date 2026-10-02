import H0mework.Versions.R2.Foundation.Runtime.Inquiry
import H0mework.Versions.R2.Probability.FullSource.Readout

/-! The existing full source field acts on complete sealed inquiry states.
Both the engine and its source activation remain inside each state basis. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry
open RootInquiryCompletion

noncomputable section
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)

abbrev Carrier := SourceOwnedObservationHistory.Carrier runtime.State
def nextState (state : runtime.State) : runtime.State := state.tick.nextState
def point (state : runtime.State) : Carrier runtime := SourceOwnedObservationHistory.sourcePoint state
def sourceAction : Carrier runtime →ₗ[ℤ] Carrier runtime :=
  SourceOwnedObservationHistory.sourceAction (nextState runtime)

abbrev Field := SourceOwnedObservationHistory.Field (nextState runtime) (point runtime)
def fieldPoint (state : runtime.State) : Field runtime :=
  SourceOwnedObservationHistory.fieldPoint (nextState runtime) (point runtime) state
abbrev fieldAction := SourceOwnedObservationHistory.fieldAction (nextState runtime) (point runtime)
abbrev word := SourceOwnedObservationHistory.FullWord.word (nextState runtime)
abbrev equivalence : Carrier runtime ≃ₗ[ℤ] Field runtime :=
  SourceOwnedObservationHistory.FullWord.equivalence (nextState runtime)

theorem point_action (state : runtime.State) :
    sourceAction runtime (point runtime state) = point runtime state.tick.nextState :=
  SourceOwnedObservationHistory.sourceAction_point (nextState runtime) state

theorem field_action (state : runtime.State) :
    fieldAction runtime (fieldPoint runtime state) = fieldPoint runtime state.tick.nextState :=
  SourceOwnedObservationHistory.fieldPoint_action (nextState runtime) (point runtime) state

theorem word_point (state : runtime.State) : word runtime (fieldPoint runtime state) = point runtime state :=
  SourceOwnedObservationHistory.FullWord.word_point (nextState runtime) state

theorem fieldPoint_injective : Function.Injective (fieldPoint runtime) :=
  SourceOwnedObservationHistory.full_fieldPoint_injective (nextState runtime)

theorem word_action (value : Field runtime) :
    word runtime (fieldAction runtime value) = sourceAction runtime (word runtime value) :=
  SourceOwnedObservationHistory.FullWord.word_action (nextState runtime) value

theorem word_source (value : Carrier runtime) : word runtime (equivalence runtime value) = value :=
  SourceOwnedObservationHistory.FullWord.word_source (nextState runtime) value

theorem source_word (value : Field runtime) : equivalence runtime (word runtime value) = value :=
  SourceOwnedObservationHistory.FullWord.source_word (nextState runtime) value

theorem actual_point_action (count : Nat) :
    sourceAction runtime (point runtime (runtime.stateAt count)) = point runtime (runtime.stateAt (count + 1)) :=
  point_action runtime (runtime.stateAt count)

theorem actual_field_action (count : Nat) :
    fieldAction runtime (fieldPoint runtime (runtime.stateAt count)) = fieldPoint runtime (runtime.stateAt (count + 1)) :=
  field_action runtime (runtime.stateAt count)

end
end SourceOperationInquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
