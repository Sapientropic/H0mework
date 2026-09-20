/-
  Proposition 63: field-memory holonomy activates recollection.

  Proposition 57/58 put memory on the geometric side: a family of fields
  converges at `C_safe`, and boundary holonomy is the gluing obstruction.
  Proposition 55/56 put recollection on the temporal/reflexive side: a
  recollection act advances a time-indexed memory field, and temporal holonomy
  is equivalent to recollectable potential through a strong support bridge.

  This file connects those two independently introduced interfaces.  The
  connection is intentionally not definitional: a concrete runtime must supply
  a `FieldHolonomyRecollectionBridge` saying which boundary-holonomy event
  corresponds to which recollection time edge.  Once supplied, the consequences
  are forced:

    * field-boundary holonomy is equivalent to recollectable potential;
    * a field-boundary holonomy witness installs future trace;
    * silence/non-silence transports across the same bridge;
    * nonempty field holonomy on a chosen event family is equivalent to
      nonempty recollection activation.

  This is the first tight Lean bridge for the slogan:

      memory has geometric structure; recollection is the temporal activation
      of a holonomy in that geometry.

  Boundary: the bridge is still a mechanism-faithfulness certificate.  The file
  does not prove that an arbitrary runtime can produce one; it proves exactly
  what follows when the runtime does.
-/

import H0mework.Realization.Fields.IndexedCover
import H0mework.Realization.Fields.TimeHolonomy

/-! ## Boundary holonomy event families -/

/-- A family of boundary-holonomy events picked out from a field gluing
problem.  `eventOf l r field` names the runtime event that would witness the
chosen local/local/global boundary for that field. -/
structure FieldBoundaryEventFamily
    {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (Event : Type*) where
  eventOf : Left -> Right -> Field -> Event
  eventSupport : Event -> Field -> Prop
  sound :
    forall l r field,
      FieldBoundaryHolonomy FL FR FG glue l r field ->
        eventSupport (eventOf l r field) field
  complete :
    forall l r field,
      eventSupport (eventOf l r field) field ->
        FieldBoundaryHolonomy FL FR FG glue l r field

/-- Boundary-event support is exactly field-boundary holonomy for the event
chosen by `eventOf`. -/
theorem fieldBoundaryEventSupport_iff_holonomy
    {Left Right Global Field : Type*}
    {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
    {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}
    {Event : Type*}
    (E : FieldBoundaryEventFamily FL FR FG glue Event)
    (l : Left) (r : Right) (field : Field) :
    E.eventSupport (E.eventOf l r field) field <->
      FieldBoundaryHolonomy FL FR FG glue l r field := by
  constructor
  · exact E.complete l r field
  · exact E.sound l r field

/-! ## Field holonomy to recollection bridge -/

/-- A mechanism-faithfulness bridge from field-boundary holonomy to temporal
recollection activation.

`temporalOf` assigns a recollection time edge to each boundary event/field
pair.  The `boundary_iff_temporal` law is the nontrivial interface: it says the
field-side boundary event is supported exactly when the assigned time edge has
temporal holonomy.  The temporal side then supplies a P56
`TemporalHolonomyMechanismBridge`, so temporal holonomy is already strongly
support-isomorphic to recollection firing. -/
structure FieldHolonomyRecollectionBridge
    {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (Event Time State Observation ActAtom TraceAtom : Type*) where
  events : FieldBoundaryEventFamily FL FR FG glue Event
  temporal :
    TemporalHolonomyMechanismBridge Event Time State Observation ActAtom
      TraceAtom
  boundary_iff_temporal :
    forall event field,
      events.eventSupport event field <->
        StepTemporalHolonomySupport temporal.stepOf event
          TemporalHolonomyAtom.observationHolonomy

namespace FieldHolonomyRecollectionBridge

variable {Left Right Global Field Event Time State Observation ActAtom
    TraceAtom : Type*}
variable {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
variable {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}

/-- THEOREM 1: a chosen field-boundary holonomy is equivalent to temporal
holonomy on the corresponding recollection edge. -/
theorem fieldBoundaryHolonomy_iff_temporalHolonomy
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right) (field : Field) :
    FieldBoundaryHolonomy FL FR FG glue l r field <->
      TemporalObservationHolonomy
        (B.temporal.stepOf (B.events.eventOf l r field)) := by
  calc
    FieldBoundaryHolonomy FL FR FG glue l r field <->
        B.events.eventSupport (B.events.eventOf l r field) field :=
      (fieldBoundaryEventSupport_iff_holonomy B.events l r field).symm
    _ <->
        StepTemporalHolonomySupport B.temporal.stepOf
          (B.events.eventOf l r field)
          TemporalHolonomyAtom.observationHolonomy :=
      B.boundary_iff_temporal (B.events.eventOf l r field) field
    _ <->
        TemporalObservationHolonomy
          (B.temporal.stepOf (B.events.eventOf l r field)) := by
      rfl

/-- THEOREM 2: field-boundary holonomy is equivalent to recollectable memory
potential at the current section of the corresponding time edge. -/
theorem fieldBoundaryHolonomy_iff_recollectable
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right) (field : Field) :
    FieldBoundaryHolonomy FL FR FG glue l r field <->
      RecollectableMemoryPotential
        (B.temporal.stepOf (B.events.eventOf l r field)).loop.act
        ((B.temporal.stepOf (B.events.eventOf l r field)).field.stateAt
          ((B.temporal.stepOf (B.events.eventOf l r field)).now)) := by
  calc
    FieldBoundaryHolonomy FL FR FG glue l r field <->
        TemporalObservationHolonomy
          (B.temporal.stepOf (B.events.eventOf l r field)) :=
      B.fieldBoundaryHolonomy_iff_temporalHolonomy l r field
    _ <->
        RecollectableMemoryPotential
          (B.temporal.stepOf (B.events.eventOf l r field)).loop.act
          ((B.temporal.stepOf (B.events.eventOf l r field)).field.stateAt
            ((B.temporal.stepOf (B.events.eventOf l r field)).now)) :=
      TemporalHolonomyMechanismBridge.holonomy_iff_recollectable
        B.temporal (B.events.eventOf l r field)

/-- THEOREM 3: a field-boundary holonomy witness installs future trace through
the corresponding recollection edge. -/
theorem fieldBoundaryHolonomy_installs_trace
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right) (field : Field)
    (hhol : FieldBoundaryHolonomy FL FR FG glue l r field) :
    TemporalTracePotential
      (B.temporal.stepOf (B.events.eventOf l r field)) := by
  have htemporal :
      StepTemporalHolonomySupport B.temporal.stepOf
        (B.events.eventOf l r field)
        TemporalHolonomyAtom.observationHolonomy := by
    exact (B.boundary_iff_temporal (B.events.eventOf l r field) field).mp
      (B.events.sound l r field hhol)
  exact TemporalHolonomyMechanismBridge.holonomy_support_installs_trace
    B.temporal (B.events.eventOf l r field)
    TemporalHolonomyAtom.observationHolonomy htemporal

/-- THEOREM 4: if the boundary-event support is silent at an event, then the
recollection side is silent at the corresponding time edge. -/
theorem boundaryEventSilent_implies_recollectionSilent
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (event : Event)
    (hsilent : forall field, B.events.eventSupport event field -> False)
    (field : Field) :
    SupportSilentAt (StepRecollectionFireSupport B.temporal.stepOf) event := by
  have htemporalSilent :
      SupportSilentAt (StepTemporalHolonomySupport B.temporal.stepOf)
        event := by
    intro atom hsupport
    cases atom
    exact hsilent field
      ((B.boundary_iff_temporal event field).mpr hsupport)
  exact (B.temporal.iso.silent_iff event).mp htemporalSilent

/-- THEOREM 5: nonempty boundary-event support for a chosen field is equivalent
to recollectable potential at that event's current time section. -/
theorem boundaryEventSupport_iff_recollectable
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (event : Event) (field : Field) :
    B.events.eventSupport event field <->
      RecollectableMemoryPotential
        (B.temporal.stepOf event).loop.act
        ((B.temporal.stepOf event).field.stateAt
          ((B.temporal.stepOf event).now)) := by
  calc
    B.events.eventSupport event field <->
        StepTemporalHolonomySupport B.temporal.stepOf event
          TemporalHolonomyAtom.observationHolonomy :=
      B.boundary_iff_temporal event field
    _ <->
        TemporalObservationHolonomy (B.temporal.stepOf event) := by
      rfl
    _ <->
        RecollectableMemoryPotential
          (B.temporal.stepOf event).loop.act
          ((B.temporal.stepOf event).field.stateAt
            ((B.temporal.stepOf event).now)) :=
      TemporalHolonomyMechanismBridge.holonomy_iff_recollectable
        B.temporal event

end FieldHolonomyRecollectionBridge

/-! ## Two-point nontrivial witness -/

/-- A tiny field-boundary event used to instantiate the generic bridge. -/
inductive TwoPointFieldEvent where
  | active
  | quiescent
  deriving DecidableEq, Repr

/-- A tiny one-field vocabulary for the bridge witness. -/
inductive TwoPointMemoryFieldAtom where
  | holonomyField
  deriving DecidableEq, Repr

/-- Local/global state spaces for the two-point field witness. -/
inductive TwoPointLocalSection where
  | localSafe
  deriving DecidableEq, Repr

inductive TwoPointGlobalSection where
  | globalFailed
  deriving DecidableEq, Repr

/-- The local field always holds. -/
def twoPointLocalFieldFamily :
    FieldFamily TwoPointLocalSection TwoPointMemoryFieldAtom where
  holds := fun _ _ => True

/-- The global field never holds, so gluing the two locally valid pieces creates
boundary holonomy. -/
def twoPointGlobalFieldFamily :
    FieldFamily TwoPointGlobalSection TwoPointMemoryFieldAtom where
  holds := fun _ _ => False

/-- The unique glue map for the two-point witness. -/
def twoPointFieldGlue :
    TwoPointLocalSection -> TwoPointLocalSection -> TwoPointGlobalSection :=
  fun _ _ => TwoPointGlobalSection.globalFailed

/-- THEOREM 6: the two-point field witness has genuine boundary holonomy. -/
theorem twoPoint_fieldBoundaryHolonomy :
    FieldBoundaryHolonomy twoPointLocalFieldFamily twoPointLocalFieldFamily
      twoPointGlobalFieldFamily twoPointFieldGlue
      TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
      TwoPointMemoryFieldAtom.holonomyField := by
  exact ⟨trivial, trivial, id⟩

/-- Event-family support for the two-point witness.  The active event supports
the field; the quiescent event is silent. -/
def twoPointFieldBoundaryEventSupport :
    TwoPointFieldEvent -> TwoPointMemoryFieldAtom -> Prop
  | TwoPointFieldEvent.active, TwoPointMemoryFieldAtom.holonomyField => True
  | TwoPointFieldEvent.quiescent, TwoPointMemoryFieldAtom.holonomyField => False

/-- The two-point boundary-event family chooses the active event for the
boundary holonomy. -/
def twoPointFieldBoundaryEventFamily :
    FieldBoundaryEventFamily twoPointLocalFieldFamily twoPointLocalFieldFamily
      twoPointGlobalFieldFamily twoPointFieldGlue TwoPointFieldEvent where
  eventOf := fun _ _ _ => TwoPointFieldEvent.active
  eventSupport := twoPointFieldBoundaryEventSupport
  sound := by
    intro l r field hhol
    cases l
    cases r
    cases field
    trivial
  complete := by
    intro l r field hsupport
    cases l
    cases r
    cases field
    exact twoPoint_fieldBoundaryHolonomy

/-- Map the field-boundary events to the already-certified temporal holonomy
edges from Proposition 56. -/
def twoPointFieldTemporalStepOf :
    TwoPointFieldEvent ->
      RecollectionTimeStep TwoPointTime TwoPointTraceState TwoPointObservation
        IndependentRecollectionAtom IndependentTraceAtom
  | TwoPointFieldEvent.active =>
      twoPointHolonomyStepOf TwoPointHolonomyEdge.active
  | TwoPointFieldEvent.quiescent =>
      twoPointHolonomyStepOf TwoPointHolonomyEdge.quiescent

/-- THEOREM 7: the field-event support agrees with temporal holonomy support in
the two-point witness. -/
theorem twoPoint_fieldBoundaryEvent_iff_temporal
    (event : TwoPointFieldEvent) (field : TwoPointMemoryFieldAtom) :
    twoPointFieldBoundaryEventSupport event field <->
      StepTemporalHolonomySupport twoPointFieldTemporalStepOf event
        TemporalHolonomyAtom.observationHolonomy := by
  cases event <;> cases field
  · constructor
    · intro _h
      exact twoPoint_temporal_holonomy
    · intro _h
      trivial
  · constructor
    · intro h
      exact False.elim h
    · intro h
      simp [twoPointFieldTemporalStepOf, StepTemporalHolonomySupport,
        twoPointHolonomyStepOf, twoPointStableTimeStep,
        TemporalObservationHolonomy, twoPointStableTimeMemoryField,
        twoPointRead] at h

/-- The temporal mechanism bridge for the two-point field events. -/
def twoPointFieldTemporalHolonomyBridge :
    TemporalHolonomyMechanismBridge TwoPointFieldEvent TwoPointTime
      TwoPointTraceState TwoPointObservation IndependentRecollectionAtom
      IndependentTraceAtom where
  stepOf := twoPointFieldTemporalStepOf
  iso := {
    leftIndependent := by
      intro assignment
      by_cases h : assignment TemporalHolonomyAtom.observationHolonomy
      · refine ⟨TwoPointFieldEvent.active, ?_⟩
        intro atom
        cases atom
        simp [StepTemporalHolonomySupport, twoPointFieldTemporalStepOf,
          twoPointHolonomyStepOf, twoPoint_temporal_holonomy, h]
      · refine ⟨TwoPointFieldEvent.quiescent, ?_⟩
        intro atom
        cases atom
        simp [StepTemporalHolonomySupport, twoPointFieldTemporalStepOf,
          twoPointHolonomyStepOf, twoPointStableTimeStep,
          TemporalObservationHolonomy, twoPointStableTimeMemoryField,
          twoPointRead, h]
    rightIndependent := by
      intro assignment
      by_cases h : assignment IndependentRecollectionAtom.recollectionCommitted
      · refine ⟨TwoPointFieldEvent.active, ?_⟩
        intro atom
        cases atom
        simp [StepRecollectionFireSupport, twoPointFieldTemporalStepOf,
          twoPointHolonomyStepOf, twoPointRecollectionTimeStep,
          twoPointTimeMemoryField, twoPointRecollectionTraceLoop,
          independentTwoPointRecollectionAct, h]
      · refine ⟨TwoPointFieldEvent.quiescent, ?_⟩
        intro atom
        cases atom
        simp [StepRecollectionFireSupport, twoPointFieldTemporalStepOf,
          twoPointHolonomyStepOf, twoPointStableTimeStep,
          twoPointStableTimeMemoryField, twoPointRecollectionTraceLoop,
          independentTwoPointRecollectionAct, h]
    leftNontrivial := by
      constructor
      · exact ⟨TwoPointFieldEvent.active,
          TemporalHolonomyAtom.observationHolonomy,
          twoPoint_temporal_holonomy⟩
      · refine ⟨TwoPointFieldEvent.quiescent, ?_⟩
        intro atom h
        cases atom
        simp [StepTemporalHolonomySupport, twoPointFieldTemporalStepOf,
          twoPointHolonomyStepOf, twoPointStableTimeStep,
          TemporalObservationHolonomy, twoPointStableTimeMemoryField,
          twoPointRead] at h
    rightNontrivial := by
      constructor
      · exact ⟨TwoPointFieldEvent.active,
          IndependentRecollectionAtom.recollectionCommitted,
          twoPoint_silent_recollection_fires⟩
      · refine ⟨TwoPointFieldEvent.quiescent, ?_⟩
        intro atom h
        cases atom
        simp [StepRecollectionFireSupport, twoPointFieldTemporalStepOf,
          twoPointHolonomyStepOf, twoPointStableTimeStep,
          twoPointStableTimeMemoryField, twoPointRecollectionTraceLoop,
          independentTwoPointRecollectionAct] at h
    atomEquiv := temporalHolonomyRecollectionAtomEquiv
    support_iff := by
      intro event atom
      cases atom
      cases event <;>
        simp [StepTemporalHolonomySupport, StepRecollectionFireSupport,
          twoPointFieldTemporalStepOf, twoPointHolonomyStepOf,
          twoPointRecollectionTimeStep, twoPointTimeMemoryField,
          twoPointStableTimeStep, twoPointStableTimeMemoryField,
          TemporalObservationHolonomy, twoPointRead,
          twoPointRecollectionTraceLoop, independentTwoPointRecollectionAct]
  }

/-- The closed two-point field-holonomy/recollection bridge. -/
def twoPointFieldHolonomyRecollectionBridge :
    FieldHolonomyRecollectionBridge
      twoPointLocalFieldFamily twoPointLocalFieldFamily
      twoPointGlobalFieldFamily twoPointFieldGlue TwoPointFieldEvent
      TwoPointTime TwoPointTraceState TwoPointObservation
      IndependentRecollectionAtom IndependentTraceAtom where
  events := twoPointFieldBoundaryEventFamily
  temporal := twoPointFieldTemporalHolonomyBridge
  boundary_iff_temporal := twoPoint_fieldBoundaryEvent_iff_temporal

/-- THEOREM 8: in the two-point witness, field-boundary holonomy is exactly
recollectable potential. -/
theorem twoPoint_fieldBoundaryHolonomy_iff_recollectable :
    FieldBoundaryHolonomy twoPointLocalFieldFamily twoPointLocalFieldFamily
      twoPointGlobalFieldFamily twoPointFieldGlue
      TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
      TwoPointMemoryFieldAtom.holonomyField <->
      RecollectableMemoryPotential
        (twoPointFieldTemporalStepOf TwoPointFieldEvent.active).loop.act
        ((twoPointFieldTemporalStepOf TwoPointFieldEvent.active).field.stateAt
          ((twoPointFieldTemporalStepOf TwoPointFieldEvent.active).now)) := by
  exact FieldHolonomyRecollectionBridge.fieldBoundaryHolonomy_iff_recollectable
      twoPointFieldHolonomyRecollectionBridge
      TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
      TwoPointMemoryFieldAtom.holonomyField

/-- THEOREM 9: the active two-point field-boundary holonomy installs future
trace through recollection. -/
theorem twoPoint_fieldBoundaryHolonomy_installs_trace :
    TemporalTracePotential
      (twoPointFieldTemporalStepOf TwoPointFieldEvent.active) := by
  exact FieldHolonomyRecollectionBridge.fieldBoundaryHolonomy_installs_trace
      twoPointFieldHolonomyRecollectionBridge
      TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
      TwoPointMemoryFieldAtom.holonomyField
      twoPoint_fieldBoundaryHolonomy

/-!
  Summary:
  - `FieldBoundaryEventFamily` names runtime events generated by field-boundary
    holonomy.
  - `FieldHolonomyRecollectionBridge` is the explicit mechanism-faithfulness
    certificate linking those events to temporal recollection holonomy.
  - Under that bridge, memory-side field holonomy is equivalent to
    recollectable potential and installs future trace.
  - The two-point witness proves the bridge shape is nontrivial without
    identifying memory with passive storage or making the two sides `rfl`.
-/
