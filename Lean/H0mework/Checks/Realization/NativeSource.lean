import H0mework.Realization.Operations.FieldInputs
import H0mework.Runtime.TraceObservation.AdditiveEdgeTraceProjectionLoss
import Mathlib.Tactic.NormNum

/-!
# Native points and their generated witnesses

The constant-one observer counts formal coefficients, not world responsibility.
It separates a sum of two points from every single native point. Actual successor
witnesses instead come from the original tick, and native edge union retains its
existing distinction from additive trace accumulation.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Controls

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}

theorem two_state_points_ne_one
    (left right candidate : process.State) :
    statePoint process left + statePoint process right ≠ statePoint process candidate := by
  intro same
  have coefficients := congrArg (observer process (fun _ => (1 : ℤ))) same
  norm_num only [map_add, observer_statePoint] at coefficients

theorem two_runtime_points_have_no_native_witness
    (left right : LivingRuntimeState process) :
    ¬ ∃ candidate : LivingRuntimeState process, point left + point right = point candidate := by
  rintro ⟨candidate, same⟩
  exact two_state_points_ne_one left.state right.state candidate.state same

theorem source_action_returns_actual_witness (runtime : LivingRuntimeState process)
    (bound : Nat) (index : Fin (bound + 1)) :
    sourceAction process (point (runtime.advance index.val)) =
        point (Field.nextWitness runtime bound index).1 ∧
      (Field.nextWitness runtime bound index).1 =
        ((SourceOperationRuntime.materialHistory runtime bound).stageAt index).next ∧
      (Field.nextWitness runtime bound index).1 = (runtime.advance index.val).tick.next :=
  ⟨sourceAction_point (runtime.advance index.val),
    Field.nextWitness_is_actual runtime bound index, rfl⟩

open RuntimeGraphResidual ResidualProjection

/-- Direct consumption of the existing whole-carrier native-overwrite counterexample. -/
example {EventId Key : Type} [DecidableEq EventId] [DecidableEq Key]
    (eventEdge : EventId → Key) (eventId : EventId) :
    ¬ ∀ state : ResidualTraceWriteBackCarrier (RuntimeGraphPendingIndicatorResidual EventId),
      runtimeGraphPendingWriteBackToEdgeTrace eventEdge
          (residualTraceWriteBackKeep (runtimeGraphPendingEraseKeep eventId) state) =
        runtimeGraphPendingEdgeSetOverwriteKeep eventEdge eventId
          (runtimeGraphPendingWriteBackToEdgeTrace eventEdge state) :=
  runtimeGraphPendingWriteBackToEdgeTrace_not_commute_nativeOverwrite eventEdge eventId

end

end SourceOperationNative.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
