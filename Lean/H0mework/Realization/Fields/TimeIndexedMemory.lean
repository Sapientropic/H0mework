/-
  Proposition 55: recollection as temporal holonomy on a memory field.

  Proposition 51 corrected the ontology: memory is recollectable potential, not
  passive storage.  Propositions 52-54 then connected recollection activation,
  future trace, and obstruction generators.

  This file adds the time-field reading.  A memory side can be specified
  independently as a time-indexed field section.  A recollection loop does not
  define that field; it advances the section along one time edge by its write.
  When the observation changes along that edge, the change is a temporal
  holonomy witness.  The core theorem says this temporal holonomy is exactly
  the local reflexive λ obstruction for the same read/write loop, and a firing
  recollection act installs trace at the next time.

  Boundary: this is the object-level holonomy skeleton.  It is not a full
  theorem about general `ρ = 1` dynamical phase residuals, limit cycles, or a
  sheaf cohomology construction.  Those richer claims need concrete dynamics
  and observation-kernel certificates.
-/

import H0mework.Realization.Fields.Maximality

/-! ## Time-indexed memory fields -/

/-- A memory field is a time-indexed section together with an observation map.
The field is independent of the reflexive query algebra; a recollection step may
later be related to it by an explicit time-edge certificate. -/
structure TimeMemoryField (Time State Observation : Type*) where
  stateAt : Time -> State
  observe : State -> Observation

/-- A recollection time step says that one edge of a time-indexed memory field
is advanced by the write of a recollection loop.  The observation map of the
field is identified with the loop's read map. -/
structure RecollectionTimeStep
    (Time State Observation ActAtom TraceAtom : Type*) where
  field : TimeMemoryField Time State Observation
  loop : RecollectionTraceLoop State Observation ActAtom TraceAtom
  now : Time
  next : Time
  observe_eq_read : forall x, field.observe x = loop.query.read x
  next_section_eq_write :
    field.stateAt next = loop.query.write (field.stateAt now)

/-- Temporal holonomy at a recollection edge: the observed value at the next
time is not the observed value at the current time. -/
def TemporalObservationHolonomy
    {Time State Observation ActAtom TraceAtom : Type*}
    (S : RecollectionTimeStep Time State Observation ActAtom TraceAtom) : Prop :=
  S.field.observe (S.field.stateAt S.next) ≠
    S.field.observe (S.field.stateAt S.now)

/-- Trace potential at the next point of a recollection time edge. -/
def TemporalTracePotential
    {Time State Observation ActAtom TraceAtom : Type*}
    (S : RecollectionTimeStep Time State Observation ActAtom TraceAtom) : Prop :=
  TracePotential S.loop (S.field.stateAt S.next)

/-! ## Holonomy is reflexive obstruction on a time edge -/

/-- THEOREM 1: if the next time section is produced by the recollection write,
temporal observation holonomy is exactly the local reflexive λ obstruction. -/
theorem temporal_holonomy_iff_reflexive_obstruction
    {Time State Observation ActAtom TraceAtom : Type*}
    (S : RecollectionTimeStep Time State Observation ActAtom TraceAtom) :
    TemporalObservationHolonomy S <->
      ReflexiveLambdaObstruction S.loop.query (S.field.stateAt S.now) := by
  simp [TemporalObservationHolonomy, ReflexiveLambdaObstruction,
    S.observe_eq_read, S.next_section_eq_write]

/-- THEOREM 2: a temporal holonomy witness gives the local no-go reason for an
unguarded/global reflexive λ certificate. -/
theorem temporal_holonomy_no_unguarded_lambda
    {Time State Observation ActAtom TraceAtom Obstruction : Type*}
    (S : RecollectionTimeStep Time State Observation ActAtom TraceAtom)
    (hhol : TemporalObservationHolonomy S) :
    UnguardedLambdaCertificate State Observation Obstruction S.loop.query ->
      False := by
  exact no_unguarded_lambda_of_observation_change
    S.loop.query
    ⟨S.field.stateAt S.now,
      (temporal_holonomy_iff_reflexive_obstruction S).mp hhol⟩

/-- THEOREM 3: if the recollection act fires at the current time, its trace is
available at the next time section. -/
theorem recollection_firing_installs_trace_at_next
    {Time State Observation ActAtom TraceAtom : Type*}
    (S : RecollectionTimeStep Time State Observation ActAtom TraceAtom)
    (atom : ActAtom)
    (hfire : S.loop.act.fires (S.field.stateAt S.now) atom) :
    TemporalTracePotential S := by
  have htrace :
      TracePotential S.loop
        (S.loop.query.write (S.field.stateAt S.now)) :=
    RecollectionTraceLoop.firing_creates_future_trace_potential
      S.loop (S.field.stateAt S.now) atom hfire
  simpa [TemporalTracePotential, S.next_section_eq_write] using htrace

/-! ## Two-point instantiation -/

/-- The smallest time axis for the temporal field witness. -/
inductive TwoPointTime where
  | before
  | after
  deriving DecidableEq, Repr

/-- The two-point field section exists independently of the recollection loop:
before has no trace mark, after has the mark. -/
def twoPointTimeMemoryField :
    TimeMemoryField TwoPointTime TwoPointTraceState TwoPointObservation where
  stateAt
    | TwoPointTime.before => TwoPointTraceState.silent
    | TwoPointTime.after => TwoPointTraceState.changed
  observe := twoPointRead

/-- The two-point recollection loop advances the memory field from `before` to
`after` by writing the trace mark. -/
def twoPointRecollectionTimeStep :
    RecollectionTimeStep TwoPointTime TwoPointTraceState TwoPointObservation
      IndependentRecollectionAtom IndependentTraceAtom where
  field := twoPointTimeMemoryField
  loop := twoPointRecollectionTraceLoop
  now := TwoPointTime.before
  next := TwoPointTime.after
  observe_eq_read := by
    intro x
    rfl
  next_section_eq_write := by
    simp [twoPointTimeMemoryField, twoPointRecollectionTraceLoop,
      twoPointReflexiveQuery, twoPointWrite]

/-- THEOREM 4: the two-point time field has nontrivial temporal holonomy. -/
theorem twoPoint_temporal_holonomy :
    TemporalObservationHolonomy twoPointRecollectionTimeStep := by
  simp [TemporalObservationHolonomy, twoPointRecollectionTimeStep,
    twoPointTimeMemoryField, twoPointRead]

/-- THEOREM 5: the two-point holonomy is exactly the familiar local reflexive
obstruction at the `before` section. -/
theorem twoPoint_temporal_holonomy_iff_reflexive :
    TemporalObservationHolonomy twoPointRecollectionTimeStep <->
      ReflexiveLambdaObstruction twoPointRecollectionTraceLoop.query
        (twoPointTimeMemoryField.stateAt TwoPointTime.before) := by
  exact temporal_holonomy_iff_reflexive_obstruction
    twoPointRecollectionTimeStep

/-- THEOREM 6: the two-point recollection act installs trace at the next time
section. -/
theorem twoPoint_temporal_holonomy_installs_trace :
    TemporalTracePotential twoPointRecollectionTimeStep := by
  exact recollection_firing_installs_trace_at_next
    twoPointRecollectionTimeStep
    IndependentRecollectionAtom.recollectionCommitted
    twoPoint_silent_recollection_fires

/-- THEOREM 7: the two-point temporal holonomy rules out an unguarded/global λ
certificate for the underlying recollection query. -/
theorem twoPoint_temporal_holonomy_no_unguarded_lambda
    (Obstruction : Type*) :
    UnguardedLambdaCertificate TwoPointTraceState TwoPointObservation
      Obstruction twoPointRecollectionTraceLoop.query -> False := by
  exact temporal_holonomy_no_unguarded_lambda
    twoPointRecollectionTimeStep twoPoint_temporal_holonomy

/-!
  Summary:
  - The memory side is a time-indexed field section.
  - The recollection side supplies an explicit time-edge update, not the field's
    ontology itself.
  - On that edge, temporal holonomy and local reflexive λ obstruction are the
    same proposition, and recollection firing installs trace at the next time.
  - This gives the `ρ = 1` / phase-holonomy discussion a precise object-level
    landing site without claiming the full dynamical theorem.
-/
