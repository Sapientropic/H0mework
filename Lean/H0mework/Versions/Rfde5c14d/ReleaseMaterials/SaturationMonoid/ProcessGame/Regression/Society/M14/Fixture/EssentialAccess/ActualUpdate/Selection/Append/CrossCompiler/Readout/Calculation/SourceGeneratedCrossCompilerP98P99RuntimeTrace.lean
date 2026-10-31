import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Runtime.SourceGeneratedCrossCompilerRelationAppendRuntime
import H0mework.Realization.Reflexive.Iteration

/-!
# P98/P99 calculation trace of the canonical cross-compiler runtime

This module reads the already sealed runtime two ticks at a time:

```text
cross action → generated selection → next cross action
```

P98 therefore recovers the exact action-state section and P99 recovers its
finite execution trace.  The query does not select an action, install a root,
or construct a second runtime; its state is the existing private
`runtime.State`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCrossCompilerP98P99RuntimeTrace

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedTenureQueueAppendRuntime
open M14SourceGeneratedCrossCompilerRelationCurrentRecurrence
open M14SourceGeneratedCrossCompilerRelationAppendPresentation
open M14SourceGeneratedSequentialCrossCompilerRelationAppend
open M14SourceGeneratedCrossCompilerRelationAppendRuntime

/-- Read-only two-tick presentation of the unique runtime. -/
def crossCompilerRuntimeReplayQuery :
    ReflexiveQuery runtime.State AnyAuthoritativeRootCurrent where
  read := fun state => state.engine.node.erase
  write := fun state => state.tick.nextState.tick.nextState

/-- The replay starts at the first heterogeneous actual-action occurrence. -/
def crossCompilerRuntimeReplayInitial : runtime.State :=
  runtime.stateAt 9

/-- P98's iterated field is exactly the cross-action subsequence of the named
runtime.  No independently supplied state field appears in the mouth. -/
theorem crossCompilerP98_stateAt_exact (depth : Nat) :
    (reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
      crossCompilerRuntimeReplayInitial).stateAt depth =
        runtime.stateAt (crossActionRuntimeDepth depth) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [reflexiveQueryIterated_stateAt_succ, inductionHypothesis]
      change
        ((runtime.stateAt (crossActionRuntimeDepth depth)).tick.nextState
            ).tick.nextState =
          runtime.stateAt (crossActionRuntimeDepth (depth + 1))
      rw [crossActionRuntimeDepth]
      rfl

/-- P98 observes the exact erased action occurrence already certified by the
cross runtime. -/
theorem crossCompilerP98_observation_exact (depth : Nat) :
    (reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
      crossCompilerRuntimeReplayInitial).observe
        ((reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
          crossCompilerRuntimeReplayInitial).stateAt depth) =
      (crossCompilerActionPresentationAt depth).erase := by
  rw [crossCompilerP98_stateAt_exact]
  change
    (runtime.stateAt (crossActionRuntimeDepth depth)).engine.node.erase =
      (crossCompilerActionPresentationAt depth).erase
  rw [crossActionState_node_exact]
  rfl

/-- P99 executes precisely the canonical P98 trace and terminates at the same
named runtime state. -/
theorem crossCompilerP99_repeatEval_exact (depth : Nat) :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive crossCompilerRuntimeReplayQuery)
        (reflexiveQueryStatefulPlan crossCompilerRuntimeReplayQuery)
        depth crossCompilerRuntimeReplayInitial
        (reflexiveQueryIteratedObservationTrace
          crossCompilerRuntimeReplayQuery crossCompilerRuntimeReplayInitial
          depth)
        (runtime.stateAt (crossActionRuntimeDepth depth)) := by
  simpa only [crossCompilerP98_stateAt_exact] using
    (reflexiveStatefulPlan_repeatEval_canonical
      crossCompilerRuntimeReplayQuery crossCompilerRuntimeReplayInitial depth)

/-- Any P99 execution of the two-tick query has the canonical finite
observation trace. -/
theorem crossCompilerP99_rows_exact
    {depth : Nat} {rows : List AnyAuthoritativeRootCurrent}
    {endpoint : runtime.State}
    (execution : StatefulGenAlg.repeatEval
      (reflexiveQueryPrimitive crossCompilerRuntimeReplayQuery)
      (reflexiveQueryStatefulPlan crossCompilerRuntimeReplayQuery)
      depth crossCompilerRuntimeReplayInitial rows endpoint) :
    rows = reflexiveQueryIteratedObservationTrace
      crossCompilerRuntimeReplayQuery crossCompilerRuntimeReplayInitial depth :=
  reflexiveStatefulPlan_repeatEval_rows_eq_trace
    crossCompilerRuntimeReplayQuery execution

/-- Any P99 execution terminates at the exact cross-action state of the same
runtime, not at a detached cursor endpoint. -/
theorem crossCompilerP99_endpoint_exact
    {depth : Nat} {rows : List AnyAuthoritativeRootCurrent}
    {endpoint : runtime.State}
    (execution : StatefulGenAlg.repeatEval
      (reflexiveQueryPrimitive crossCompilerRuntimeReplayQuery)
      (reflexiveQueryStatefulPlan crossCompilerRuntimeReplayQuery)
      depth crossCompilerRuntimeReplayInitial rows endpoint) :
    endpoint = runtime.stateAt (crossActionRuntimeDepth depth) :=
  (reflexiveStatefulPlan_repeatEval_final_state
    crossCompilerRuntimeReplayQuery execution).trans
      (crossCompilerP98_stateAt_exact depth)

/-- The calculation trace consumes, but never replaces, the actual-action
runtime receipt at the same finite depth. -/
theorem crossCompilerP98P99_directConsumer (depth : Nat) :
    (reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
        crossCompilerRuntimeReplayInitial).stateAt depth =
        runtime.stateAt (9 + 2 * depth) ∧
      (reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
        crossCompilerRuntimeReplayInitial).observe
          ((reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
            crossCompilerRuntimeReplayInitial).stateAt depth) =
        (crossCompilerActionPresentationAt depth).erase ∧
      StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive crossCompilerRuntimeReplayQuery)
        (reflexiveQueryStatefulPlan crossCompilerRuntimeReplayQuery)
        depth crossCompilerRuntimeReplayInitial
        (reflexiveQueryIteratedObservationTrace
          crossCompilerRuntimeReplayQuery crossCompilerRuntimeReplayInitial
          depth)
        (runtime.stateAt (9 + 2 * depth)) ∧
      SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
        (generatedCrossCompilerRelationAppendActionAt depth)
        runtime (9 + 2 * depth) ∧
      type_of% (crossCompilerRuntime_directConsumer depth) := by
  rw [← crossActionRuntimeDepth_closed depth]
  exact ⟨crossCompilerP98_stateAt_exact depth,
    crossCompilerP98_observation_exact depth,
    crossCompilerP99_repeatEval_exact depth,
    crossActionRuntimeResumption depth,
    crossCompilerRuntime_directConsumer depth⟩

/-- Three renewals return to the same folded relation seed at a later actual
path, but P98 still observes a different occurrence. -/
theorem periodThreeSeed_doesNotCollapseP98Occurrence (depth : Nat) :
    (crossCompilerCurrentStageAt (depth + 3)).targetSeed =
        (crossCompilerCurrentStageAt depth).targetSeed ∧
      (reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
        crossCompilerRuntimeReplayInitial).observe
          ((reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
            crossCompilerRuntimeReplayInitial).stateAt (depth + 3)) ≠
        (reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
          crossCompilerRuntimeReplayInitial).observe
            ((reflexiveQueryIteratedTimeField crossCompilerRuntimeReplayQuery
              crossCompilerRuntimeReplayInitial).stateAt depth) := by
  refine ⟨(periodThreeSeed_differentCrossCompilerOccurrence depth).1, ?_⟩
  rw [crossCompilerP98_observation_exact,
    crossCompilerP98_observation_exact]
  exact (periodThreeSeed_differentCrossCompilerOccurrence depth).2

end
end M14SourceGeneratedCrossCompilerP98P99RuntimeTrace
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerP98P99RuntimeTrace.crossCompilerP98_stateAt_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerP98P99RuntimeTrace.crossCompilerP98_observation_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerP98P99RuntimeTrace.crossCompilerP99_repeatEval_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerP98P99RuntimeTrace.crossCompilerP98P99_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCrossCompilerP98P99RuntimeTrace.periodThreeSeed_doesNotCollapseP98Occurrence
