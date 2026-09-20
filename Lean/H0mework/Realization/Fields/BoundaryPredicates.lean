/-
  Proposition 64: the field/recollection bridge as a Prop-valued pullback.

  Proposition 63 gave a mechanism-faithfulness bridge:

      field-boundary holonomy event  <->  temporal holonomy edge
                                      <->  recollection activation

  This file strengthens the reading of that bridge.  It is not merely an
  adapter from one vocabulary to another.  Once the mechanism bridge is
  supplied, the geometric memory side and the recollection side form a
  Prop-valued fiber product over the common temporal-holonomy predicate.

  In other words:

      memory-side boundary field support
        ×_{temporal holonomy}
      recollection-side activation

  is canonically equivalent to temporal holonomy itself, and it has the expected
  greatest-cone/universal property at this Prop level.

  Boundary: this is still a Prop-valued pullback/fiber object, not a full sheaf
  cohomology or descent theorem in a category of sections.  The runtime still
  has to supply the P63 bridge.
-/

import H0mework.Realization.Fields.BoundaryEvents

/-! ## The three predicates over a boundary-event space -/

/-- The memory/geometric side: the chosen boundary field is supported at this
runtime event. -/
def BoundaryEventSupportForField
    {Left Right Global Field Event Time State Observation ActAtom TraceAtom :
      Type*}
    {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
    {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (event : Event) : Prop :=
  B.events.eventSupport event field

/-- The common base predicate: the assigned time edge has temporal holonomy. -/
def TemporalHolonomyAtEvent
    {Left Right Global Field Event Time State Observation ActAtom TraceAtom :
      Type*}
    {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
    {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (event : Event) : Prop :=
  TemporalObservationHolonomy (B.temporal.stepOf event)

/-- The recollection side: the recollection act has potential at the current
section of the assigned time edge. -/
def RecollectionPotentialAtEvent
    {Left Right Global Field Event Time State Observation ActAtom TraceAtom :
      Type*}
    {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
    {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (event : Event) : Prop :=
  RecollectableMemoryPotential
    (B.temporal.stepOf event).loop.act
    ((B.temporal.stepOf event).field.stateAt
      ((B.temporal.stepOf event).now))

namespace FieldHolonomyRecollectionBridge

variable {Left Right Global Field Event Time State Observation ActAtom
    TraceAtom : Type*}
variable {FL : FieldFamily Left Field} {FR : FieldFamily Right Field}
variable {FG : FieldFamily Global Field} {glue : Left -> Right -> Global}

/-- THEOREM 1: the memory/geometric side maps to the common temporal-holonomy
base. -/
theorem boundaryEventSupportForField_iff_temporal
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (event : Event) :
    BoundaryEventSupportForField B field event <->
      TemporalHolonomyAtEvent B event := by
  calc
    BoundaryEventSupportForField B field event <->
        StepTemporalHolonomySupport B.temporal.stepOf event
          TemporalHolonomyAtom.observationHolonomy :=
      B.boundary_iff_temporal event field
    _ <-> TemporalHolonomyAtEvent B event := by
      rfl

/-- THEOREM 2: the recollection side maps to the same temporal-holonomy base. -/
theorem recollectionPotentialAtEvent_iff_temporal
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (event : Event) :
    RecollectionPotentialAtEvent B event <->
      TemporalHolonomyAtEvent B event := by
  exact (TemporalHolonomyMechanismBridge.holonomy_iff_recollectable
    B.temporal event).symm

/-! ## The Prop-valued fiber product -/

/-- The Prop-valued pullback/fiber product of memory-side boundary support and
recollection-side activation over temporal holonomy. -/
def HolonomyActivationPullback
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (event : Event) : Prop :=
  BoundaryEventSupportForField B field event /\
    RecollectionPotentialAtEvent B event

/-- THEOREM 3: the fiber product is canonically equivalent to the common
temporal-holonomy base. -/
theorem holonomyActivationPullback_iff_temporal
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (event : Event) :
    HolonomyActivationPullback B field event <->
      TemporalHolonomyAtEvent B event := by
  constructor
  · intro h
    exact (boundaryEventSupportForField_iff_temporal B field event).mp h.1
  · intro htemporal
    exact ⟨
      (boundaryEventSupportForField_iff_temporal B field event).mpr htemporal,
      (recollectionPotentialAtEvent_iff_temporal B event).mpr htemporal
    ⟩

/-- THEOREM 4: the pullback also presents the memory/geometric side. -/
theorem holonomyActivationPullback_iff_boundarySupport
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (event : Event) :
    HolonomyActivationPullback B field event <->
      BoundaryEventSupportForField B field event := by
  calc
    HolonomyActivationPullback B field event <->
        TemporalHolonomyAtEvent B event :=
      holonomyActivationPullback_iff_temporal B field event
    _ <-> BoundaryEventSupportForField B field event :=
      (boundaryEventSupportForField_iff_temporal B field event).symm

/-- THEOREM 5: the pullback presents the recollection side as well. -/
theorem holonomyActivationPullback_iff_recollectionPotential
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (event : Event) :
    HolonomyActivationPullback B field event <->
      RecollectionPotentialAtEvent B event := by
  calc
    HolonomyActivationPullback B field event <->
        TemporalHolonomyAtEvent B event :=
      holonomyActivationPullback_iff_temporal B field event
    _ <-> RecollectionPotentialAtEvent B event :=
      (recollectionPotentialAtEvent_iff_temporal B event).symm

/-! ## Universal property at the Prop level -/

/-- A domain maps into both sides of the span when every event in it supports
the chosen memory-side field and also has recollection potential. -/
def HolonomyActivationCone
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (D : Event -> Prop) : Prop :=
  (forall event, D event -> BoundaryEventSupportForField B field event) /\
    (forall event, D event -> RecollectionPotentialAtEvent B event)

/-- THEOREM 6: a cone into both sides is exactly inclusion into the pullback
predicate. -/
theorem holonomyActivationCone_iff_subset_pullback
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (D : Event -> Prop) :
    HolonomyActivationCone B field D <->
      PredSubset D (HolonomyActivationPullback B field) := by
  constructor
  · intro h event hD
    exact ⟨h.1 event hD, h.2 event hD⟩
  · intro h
    constructor
    · intro event hD
      exact (h event hD).1
    · intro event hD
      exact (h event hD).2

/-- THEOREM 7: the same cone condition is exactly inclusion into the common
temporal-holonomy base. -/
theorem holonomyActivationCone_iff_subset_temporal
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) (D : Event -> Prop) :
    HolonomyActivationCone B field D <->
      PredSubset D (TemporalHolonomyAtEvent B) := by
  constructor
  · intro h event hD
    exact (holonomyActivationPullback_iff_temporal B field event).mp
      ((holonomyActivationCone_iff_subset_pullback B field D).mp h event hD)
  · intro h
    exact (holonomyActivationCone_iff_subset_pullback B field D).mpr
      (fun event hD =>
        (holonomyActivationPullback_iff_temporal B field event).mpr
          (h event hD))

/-- THEOREM 8: the pullback is the greatest cone into the memory/recollection
span. -/
theorem holonomyActivationPullback_greatest_cone
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) :
    forall D : Event -> Prop,
      HolonomyActivationCone B field D ->
        PredSubset D (HolonomyActivationPullback B field) := by
  intro D hD
  exact (holonomyActivationCone_iff_subset_pullback B field D).mp hD

/-- THEOREM 9: the pullback itself is a cone into both sides. -/
theorem holonomyActivationPullback_is_cone
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (field : Field) :
    HolonomyActivationCone B field
      (HolonomyActivationPullback B field) := by
  exact (holonomyActivationCone_iff_subset_pullback B field
    (HolonomyActivationPullback B field)).mpr
    (fun event h => h)

/-! ## Returning to concrete local/glued field holonomy -/

/-- The local/glued field-boundary event, read as the pullback of geometric
memory holonomy and recollection activation. -/
def ChosenFieldBoundaryActivation
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right) (field : Field) : Prop :=
  HolonomyActivationPullback B field (B.events.eventOf l r field)

/-- THEOREM 10: at a concrete local/glued boundary, the pullback is exactly
field-boundary holonomy. -/
theorem chosenFieldBoundaryActivation_iff_boundaryHolonomy
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right) (field : Field) :
    ChosenFieldBoundaryActivation B l r field <->
      FieldBoundaryHolonomy FL FR FG glue l r field := by
  calc
    ChosenFieldBoundaryActivation B l r field <->
        BoundaryEventSupportForField B field (B.events.eventOf l r field) :=
      holonomyActivationPullback_iff_boundarySupport B field
        (B.events.eventOf l r field)
    _ <-> FieldBoundaryHolonomy FL FR FG glue l r field :=
      fieldBoundaryEventSupport_iff_holonomy B.events l r field

/-- THEOREM 11: an active local/glued boundary pullback installs future trace. -/
theorem chosenFieldBoundaryActivation_installs_trace
    (B :
      FieldHolonomyRecollectionBridge FL FR FG glue Event Time State
        Observation ActAtom TraceAtom)
    (l : Left) (r : Right) (field : Field)
    (hactivation : ChosenFieldBoundaryActivation B l r field) :
    TemporalTracePotential (B.temporal.stepOf (B.events.eventOf l r field)) := by
  exact FieldHolonomyRecollectionBridge.fieldBoundaryHolonomy_installs_trace
    B l r field
    ((chosenFieldBoundaryActivation_iff_boundaryHolonomy B l r field).mp
      hactivation)

end FieldHolonomyRecollectionBridge

/-! ## Two-point witness -/

/-- THEOREM 12: the two-point bridge's active event realizes the pullback
exactly when it realizes temporal holonomy. -/
theorem twoPoint_holonomyActivationPullback_iff_temporal :
      FieldHolonomyRecollectionBridge.HolonomyActivationPullback
      twoPointFieldHolonomyRecollectionBridge
      TwoPointMemoryFieldAtom.holonomyField
      TwoPointFieldEvent.active <->
      TemporalHolonomyAtEvent
        twoPointFieldHolonomyRecollectionBridge
        TwoPointFieldEvent.active := by
  exact FieldHolonomyRecollectionBridge.holonomyActivationPullback_iff_temporal
    twoPointFieldHolonomyRecollectionBridge
    TwoPointMemoryFieldAtom.holonomyField
    TwoPointFieldEvent.active

/-- THEOREM 13: the active two-point local/glued boundary activation installs
future trace through the pullback theorem. -/
theorem twoPoint_chosenFieldBoundaryActivation_installs_trace :
    TemporalTracePotential
      (twoPointFieldTemporalStepOf TwoPointFieldEvent.active) := by
  have hactivation :
      FieldHolonomyRecollectionBridge.ChosenFieldBoundaryActivation
        twoPointFieldHolonomyRecollectionBridge
        TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
        TwoPointMemoryFieldAtom.holonomyField := by
    exact (FieldHolonomyRecollectionBridge.chosenFieldBoundaryActivation_iff_boundaryHolonomy
        twoPointFieldHolonomyRecollectionBridge
        TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
        TwoPointMemoryFieldAtom.holonomyField).mpr
      twoPoint_fieldBoundaryHolonomy
  exact FieldHolonomyRecollectionBridge.chosenFieldBoundaryActivation_installs_trace
      twoPointFieldHolonomyRecollectionBridge
      TwoPointLocalSection.localSafe TwoPointLocalSection.localSafe
      TwoPointMemoryFieldAtom.holonomyField hactivation

/-!
  Summary:
  - `HolonomyActivationPullback` is the Prop-valued fiber product of the
    memory/geometric field-boundary side and the recollection side over temporal
    holonomy.
  - The pullback is equivalent to temporal holonomy and has the expected
    greatest-cone universal property.
  - At a concrete local/glued boundary, the pullback is exactly
    `FieldBoundaryHolonomy`, and activation through that pullback installs
    future trace.
-/
