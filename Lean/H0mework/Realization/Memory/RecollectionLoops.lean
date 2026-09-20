/-
  Proposition 52: recollection installs future trace.

  Proposition 51 put the reflexivity-memory isomorphism at the right layer:
  reflexive algebra corresponds to recollection activation, while memory is
  recollectable potential rather than passive storage.  This file adds the
  temporal part of the claim:

      recollection is not just a read;
      a recollection act can write a trace;
      the written trace becomes available to future recall.

  This is the algebraic shape behind "a divination-like consultation is a
  recollection act": it does not merely read a static book; it writes a new
  trace that can be recalled later.

  Boundary: this file proves the finite trace-installing shape.  It does not
  claim that any concrete Yi/runtime implementation has supplied the
  mechanism-faithfulness certificate for its real trace reducer.
-/

import H0mework.Realization.Memory.StorageDistinction

/-! ## Recollection trace loops -/

/-- A recollection trace loop packages three layers:

* a reflexive read/write query;
* an activation act that may fire before the write;
* a trace availability predicate after the write.

The key law says that every firing act installs a corresponding trace in the
next state. -/
structure RecollectionTraceLoop
    (State Observation ActAtom TraceAtom : Type*) where
  query : ReflexiveQuery State Observation
  act : RecollectionAct State ActAtom
  traceAvailable : State -> TraceAtom -> Prop
  traceOf : ActAtom -> TraceAtom
  installs :
    forall x atom, act.fires x atom ->
      traceAvailable (query.write x) (traceOf atom)

/-- A state has trace potential when some trace is available there. -/
def TracePotential {State Observation ActAtom TraceAtom : Type*}
    (loop : RecollectionTraceLoop State Observation ActAtom TraceAtom)
    (x : State) : Prop :=
  exists trace, loop.traceAvailable x trace

namespace RecollectionTraceLoop

variable {State Observation ActAtom TraceAtom : Type*}

/-- THEOREM 1: every recollection firing installs future trace. -/
theorem firing_installs_future_trace
    (loop : RecollectionTraceLoop State Observation ActAtom TraceAtom)
    (x : State) (atom : ActAtom)
    (hfire : loop.act.fires x atom) :
    loop.traceAvailable (loop.query.write x) (loop.traceOf atom) :=
  loop.installs x atom hfire

/-- THEOREM 2: every recollection firing creates future trace potential. -/
theorem firing_creates_future_trace_potential
    (loop : RecollectionTraceLoop State Observation ActAtom TraceAtom)
    (x : State) (atom : ActAtom)
    (hfire : loop.act.fires x atom) :
    TracePotential loop (loop.query.write x) :=
  ⟨loop.traceOf atom, loop.installs x atom hfire⟩

end RecollectionTraceLoop

/-! ## Two-point trace-installing witness -/

/-- The trace made available after a recollection act. -/
inductive IndependentTraceAtom where
  | traceAvailable
  deriving DecidableEq, Repr

/-- In the two-point witness, the written/changed state carries the trace; the
silent state does not. -/
def twoPointTraceAvailable :
    TwoPointTraceState -> IndependentTraceAtom -> Prop
  | TwoPointTraceState.silent, IndependentTraceAtom.traceAvailable => False
  | TwoPointTraceState.changed, IndependentTraceAtom.traceAvailable => True

/-- Map the independent recollection act atom to the trace it installs. -/
def twoPointTraceOf :
    IndependentRecollectionAtom -> IndependentTraceAtom
  | IndependentRecollectionAtom.recollectionCommitted =>
      IndependentTraceAtom.traceAvailable

/-- The two-point recollection loop: the silent state can activate a
recollection act; the write marks the state; the marked state carries the
future trace. -/
def twoPointRecollectionTraceLoop :
    RecollectionTraceLoop TwoPointTraceState TwoPointObservation
      IndependentRecollectionAtom IndependentTraceAtom where
  query := twoPointReflexiveQuery
  act := independentTwoPointRecollectionAct
  traceAvailable := twoPointTraceAvailable
  traceOf := twoPointTraceOf
  installs := by
    intro x atom hfire
    cases x <;> cases atom <;>
      simp [independentTwoPointRecollectionAct, twoPointTraceAvailable,
        twoPointTraceOf, twoPointReflexiveQuery, twoPointWrite] at hfire ⊢

/-- THEOREM 3: the silent state initially has no trace. -/
theorem twoPoint_silent_has_no_trace :
    ¬ TracePotential twoPointRecollectionTraceLoop TwoPointTraceState.silent := by
  rintro ⟨trace, htrace⟩
  cases trace
  exact htrace

/-- THEOREM 4: the silent state can fire a recollection act. -/
theorem twoPoint_silent_recollection_fires :
    twoPointRecollectionTraceLoop.act.fires
      TwoPointTraceState.silent
      IndependentRecollectionAtom.recollectionCommitted := by
  simp [twoPointRecollectionTraceLoop, independentTwoPointRecollectionAct]

/-- THEOREM 5: after the silent state's recollection act writes, trace
potential is available in the next state. -/
theorem twoPoint_silent_recollection_installs_future_trace :
    TracePotential twoPointRecollectionTraceLoop
      (twoPointRecollectionTraceLoop.query.write TwoPointTraceState.silent) := by
  exact RecollectionTraceLoop.firing_creates_future_trace_potential
    twoPointRecollectionTraceLoop
    TwoPointTraceState.silent
    IndependentRecollectionAtom.recollectionCommitted
    twoPoint_silent_recollection_fires

/-- THEOREM 6: the written/changed state has trace potential. -/
theorem twoPoint_changed_has_trace :
    TracePotential twoPointRecollectionTraceLoop TwoPointTraceState.changed := by
  exact ⟨IndependentTraceAtom.traceAvailable, trivial⟩

/-- THEOREM 7: available trace is still not the same thing as a currently
firing recollection act.  The changed state carries trace, but the independent
recollection act no longer fires there. -/
theorem twoPoint_trace_available_without_current_fire :
    TracePotential twoPointRecollectionTraceLoop TwoPointTraceState.changed /\
      ¬ RecollectableMemoryPotential
        twoPointRecollectionTraceLoop.act TwoPointTraceState.changed := by
  constructor
  · exact twoPoint_changed_has_trace
  · rintro ⟨atom, hfire⟩
    cases atom
    exact hfire

/-- THEOREM 8: the two-point witness has a temporal arrow: no trace before,
recollection activation at the current state, trace after the write. -/
theorem twoPoint_recollection_temporal_arrow :
    (¬ TracePotential twoPointRecollectionTraceLoop TwoPointTraceState.silent) /\
      RecollectableMemoryPotential
        twoPointRecollectionTraceLoop.act TwoPointTraceState.silent /\
      TracePotential twoPointRecollectionTraceLoop
        (twoPointRecollectionTraceLoop.query.write TwoPointTraceState.silent) := by
  constructor
  · exact twoPoint_silent_has_no_trace
  · constructor
    · exact ⟨IndependentRecollectionAtom.recollectionCommitted,
        twoPoint_silent_recollection_fires⟩
    · exact twoPoint_silent_recollection_installs_future_trace

/-!
  Summary:
  - `RecollectionTraceLoop` is the time-aware layer missing from passive
    storage: act firing before the write installs trace after the write.
  - The two-point witness proves the temporal pattern directly: no trace
    before, recollection activation now, trace potential after the write.
  - The trace can be available even when the current act is no longer firing,
    so trace availability and recollection activation remain distinct layers.
-/
