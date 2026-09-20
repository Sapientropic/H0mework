/-
  Proposition 67: memory as seven-field convergence.

  The preceding propositions split the foundation into two independent
  lineages:

    * geometry: the seven AIppocampus safety facets are Prop-valued fields,
      with restriction, descent, and boundary holonomy (P57-P60);
    * reflexive computation: recollection is a read/write activation over a
      time-indexed memory field, and a mechanism bridge connects temporal
      holonomy to recollectable potential (P55-P65).

  This file records the corrected ontology:

      memory is not an unstructured stored state;
      memory is the convergence locus of fields, and recollection is a
      temporal activation of field-boundary holonomy.

  It does not claim full sheaf cohomology.  It gives the current Prop-valued
  fiber/descent theorem: `C_safe` is the universal seven-field convergence
  object; gluing failure is boundary holonomy; and, under the already-explicit
  mechanism bridge, boundary holonomy is recollection activation that installs
  future trace.
-/

import H0mework.Realization.Memory.ObstructionEquivalence

/-! ## The seven-field fiber object -/

/-- A Prop-valued fiber product / cone object for the seven semantic fields.

`carrier` is a candidate convergence locus.  The projection law says every
point in the carrier satisfies every semantic field.  The greatest law says
any other predicate satisfying every semantic field factors through the
carrier. -/
structure SevenFieldFiberProduct {State : Type*}
    (P : CSafePredicates State) where
  carrier : State -> Prop
  project :
    forall x, carrier x ->
      forall field, (semanticFieldFamily P).holds field x
  greatest :
    forall D : State -> Prop,
      (forall x, D x -> forall field, (semanticFieldFamily P).holds field x) ->
        PredSubset D carrier

namespace SevenFieldFiberProduct

variable {State : Type*}
variable {P : CSafePredicates State}

/-- THEOREM 1: any two seven-field fiber objects have equivalent carriers.
This is the Prop-valued universal property of the convergence locus. -/
theorem carrier_equiv
    (A B : SevenFieldFiberProduct P) (x : State) :
    A.carrier x <-> B.carrier x := by
  constructor
  · intro hx
    exact B.greatest A.carrier (fun y hy field => A.project y hy field) x hx
  · intro hx
    exact A.greatest B.carrier (fun y hy field => B.project y hy field) x hx

end SevenFieldFiberProduct

/-- `C_safe` as the universal convergence/fiber object of the seven
AIppocampus fields. -/
def cSafeSevenFieldFiberProduct {State : Type*}
    (P : CSafePredicates State) : SevenFieldFiberProduct P where
  carrier := CSafe P
  project := by
    intro x hx field
    exact ((semanticFieldConvergence_iff_csafe P x).mpr hx) field
  greatest := by
    intro D hD x hx
    exact (semanticFieldConvergence_iff_csafe P x).mp (hD x hx)

/-- THEOREM 2: the carrier of the canonical seven-field fiber product is
exactly `C_safe`. -/
theorem cSafeSevenFieldFiberProduct_carrier_iff
    {State : Type*} (P : CSafePredicates State) (x : State) :
    (cSafeSevenFieldFiberProduct P).carrier x <-> CSafe P x := by
  rfl

/-- THEOREM 3: every presentation of the seven-field fiber product is uniquely
equivalent to `C_safe`. -/
theorem sevenFieldFiberProduct_unique_to_csafe
    {State : Type*} (P : CSafePredicates State)
    (F : SevenFieldFiberProduct P) (x : State) :
    F.carrier x <-> CSafe P x := by
  exact SevenFieldFiberProduct.carrier_equiv F
    (cSafeSevenFieldFiberProduct P) x

/-- THEOREM 4: the older `FieldConvergenceObject` presentation and the
seven-field fiber-product presentation have the same carrier. -/
theorem sevenFieldFiberProduct_matches_convergenceObject
    {State : Type*} (P : CSafePredicates State) (x : State) :
    (cSafeFieldConvergenceObject P).carrier x <->
      (cSafeSevenFieldFiberProduct P).carrier x := by
  rfl

/-! ## Boundary holonomy as the geometric memory obstruction -/

/-- Semantic memory-field boundary holonomy for a local/local/global gluing
attempt. -/
abbrev SemanticMemoryFieldBoundaryHolonomy
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (field : SemanticAtom) : Prop :=
  FieldBoundaryHolonomy
    (semanticFieldFamily PL) (semanticFieldFamily PR)
    (semanticFieldFamily PG) glue l r field

/-- THEOREM 5: if local pieces converge, global failure is exactly nonempty
semantic memory-field boundary holonomy. -/
theorem semanticMemoryFieldBoundaryHolonomy_nonempty_iff_global_unsafe
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right)
    (hl : CSafe PL l) (hr : CSafe PR r) :
    (exists field,
      SemanticMemoryFieldBoundaryHolonomy PL PR PG glue l r field) <->
      Not (CSafe PG (glue l r)) := by
  exact semanticFieldBoundaryHolonomy_nonempty_iff_global_unsafe
    PL PR PG glue l r hl hr

/-- THEOREM 6: semantic memory-field boundary holonomy is exactly the older
gluing-failure support object.  The taxonomy is a presentation of this
geometric support, not its source. -/
theorem semanticMemoryFieldBoundaryHolonomy_iff_gluingFailureSupport
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (field : SemanticAtom) :
    SemanticMemoryFieldBoundaryHolonomy PL PR PG glue l r field <->
      GluingFailureSupport PL PR PG glue l r field := by
  exact semanticFieldBoundaryHolonomy_iff_gluingFailureSupport
    PL PR PG glue l r field

/-- THEOREM 7: the graph cross-critical-pair generator is the graph field's
cross-boundary holonomy, once the runtime supplies the graph cocycle bridge. -/
theorem graphCrossCriticalPair_is_memoryFieldHolonomy
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (C : GraphGluingCocycle)
    (hL :
      semanticHolds PL SemanticAtom.graphConfluence l ↔ C.leftConfluent)
    (hR :
      semanticHolds PR SemanticAtom.graphConfluence r ↔ C.rightConfluent)
    (hG :
      semanticHolds PG SemanticAtom.graphConfluence (glue l r) ↔
        C.globalConfluent) :
    SemanticMemoryFieldBoundaryHolonomy PL PR PG glue l r
        SemanticAtom.graphConfluence <->
      GraphH1Generator C := by
  exact graph_fieldBoundaryHolonomy_iff_h1_generator
    PL PR PG glue l r C hL hR hG

/-! ## Recollection as activation of the geometric obstruction -/

/-- THEOREM 8: under the P63/P64 mechanism bridge, local `C_safe` plus global
`¬ C_safe` is exactly nonempty semantic field activation. -/
theorem semanticMemoryFieldActivation_nonempty_iff_global_unsafe
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    {Event Time State Observation ActAtom TraceAtom : Type*}
    (B :
      FieldHolonomyRecollectionBridge
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue Event Time State Observation ActAtom
        TraceAtom)
    (l : Left) (r : Right)
    (hl : CSafe PL l) (hr : CSafe PR r) :
    (exists field,
      FieldHolonomyRecollectionBridge.ChosenFieldBoundaryActivation
        B l r field) <->
      Not (CSafe PG (glue l r)) := by
  exact FieldHolonomyRecollectionBridge.semanticChosenActivation_nonempty_iff_global_unsafe
    PL PR PG glue B l r hl hr

/-- THEOREM 9: under the same bridge, a global seven-field gluing failure
installs future trace through recollection. -/
theorem semanticMemoryFieldGluingFailure_installs_trace
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    {Event Time State Observation ActAtom TraceAtom : Type*}
    (B :
      FieldHolonomyRecollectionBridge
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue Event Time State Observation ActAtom
        TraceAtom)
    (l : Left) (r : Right)
    (hl : CSafe PL l) (hr : CSafe PR r)
    (hfail : Not (CSafe PG (glue l r))) :
    exists field,
      TemporalTracePotential
        (B.temporal.stepOf (B.events.eventOf l r field)) := by
  exact FieldHolonomyRecollectionBridge.semanticGlobalUnsafe_installs_trace
    PL PR PG glue B l r hl hr hfail

/-!
  Summary:
  - The seven AIppocampus facets are formally fields in the current Prop-valued
    geometry.
  - `C_safe` is their universal convergence/fiber object, not merely an
    arbitrary conjunction label.
  - Cross-boundary gluing failure is semantic memory-field holonomy; the graph
    cross-critical-pair generator is the graph instance of that holonomy.
  - Under the explicit P63/P64 bridge, the holonomy activates recollection and
    installs future trace.

  Remaining boundary:
  - This is still Prop-valued field geometry.  The real sheaf-theoretic upgrade
    is to replace field predicates with section objects over opens, prove
    functorial restriction/descent laws, and quotient higher overlap residuals
    into an actual cohomology object.
-/
