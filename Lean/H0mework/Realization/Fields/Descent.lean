/-
  Proposition 58: field descent failures and boundary holonomy.

  Proposition 57 recast the seven `C_safe` facets as a Prop-valued field
  convergence object.  This file adds the first descent/gluing layer for that
  geometry.

  The construction is still deliberately thin: a `FieldDescentWitness` says
  each local field can be glued into the corresponding global field.  If such a
  witness is missing, the canonical obstruction is a field that holds on both
  local pieces but fails on the glued global piece.  That is the Prop-valued
  version of boundary holonomy.

  For AIppocampus, this generic field-descent failure is definitionally the
  old `GluingFailureSupport`; the graph field's boundary holonomy is therefore
  exactly the cross-critical-pair generator from Proposition 17.

  Boundary: this is a descent skeleton, not full sheaf theory.  It has local
  pieces and a glue map, but not arbitrary covers, restriction functor laws, or
  cochain/cohomology groups.
-/

import H0mework.Realization.Fields.PropositionalFamily

/-! ## Generic field descent -/

/-- A local-to-global field descent witness: whenever a field holds on both
local pieces, it holds on the glued global piece. -/
structure FieldDescentWitness {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global) where
  descend :
    forall field l r,
      FL.holds field l ->
      FR.holds field r ->
      FG.holds field (glue l r)

/-- THEOREM 1: a descent witness sends two locally convergent states to a
globally convergent glued state. -/
theorem fieldConvergence_preserved_by_descent
    {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (hdesc : FieldDescentWitness FL FR FG glue) :
    forall l r,
      FieldConvergence FL l ->
      FieldConvergence FR r ->
      FieldConvergence FG (glue l r) := by
  intro l r hl hr field
  exact hdesc.descend field l r (hl field) (hr field)

/-- Boundary holonomy for a field family: a field is locally present on both
pieces but fails after gluing. -/
def FieldBoundaryHolonomy {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (field : Field) : Prop :=
  FL.holds field l /\ FR.holds field r /\
    Not (FG.holds field (glue l r))

/-- THEOREM 2: when both local pieces converge, global non-convergence is
exactly nonempty boundary holonomy. -/
theorem fieldBoundaryHolonomy_nonempty_iff_local_convergent_global_failed
    {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (l : Left) (r : Right)
    (hl : FieldConvergence FL l) (hr : FieldConvergence FR r) :
    (exists field, FieldBoundaryHolonomy FL FR FG glue l r field) <->
      Not (FieldConvergence FG (glue l r)) := by
  constructor
  · rintro ⟨field, _hL, _hR, hfail⟩ hconv
    exact hfail (hconv field)
  · intro hnot
    rcases (fieldFailure_nonempty_iff_not_convergent FG (glue l r)).mpr
      hnot with ⟨field, hfail⟩
    exact ⟨field, hl field, hr field, hfail⟩

/-- THEOREM 3: a descent witness rules out boundary holonomy. -/
theorem no_fieldBoundaryHolonomy_of_descent
    {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (hdesc : FieldDescentWitness FL FR FG glue) :
    forall l r field,
      Not (FieldBoundaryHolonomy FL FR FG glue l r field) := by
  intro l r field hhol
  exact hhol.2.2 (hdesc.descend field l r hhol.1 hhol.2.1)

/-- THEOREM 4: nonempty boundary holonomy refutes any descent witness for the
same field family and glue map. -/
theorem boundaryHolonomy_refutes_descent
    {Left Right Global Field : Type*}
    (FL : FieldFamily Left Field) (FR : FieldFamily Right Field)
    (FG : FieldFamily Global Field) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (field : Field)
    (hhol : FieldBoundaryHolonomy FL FR FG glue l r field) :
    Not (FieldDescentWitness FL FR FG glue) := by
  intro hdesc
  exact no_fieldBoundaryHolonomy_of_descent FL FR FG glue hdesc l r field hhol

/-! ## AIppocampus seven-field descent -/

/-- THEOREM 5: the P17 gluing witness is the seven-field descent witness for
the semantic field family. -/
theorem cSafeGluingWitness_to_fieldDescent
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (hglue : CSafeGluingWitness PL PR PG glue) :
    FieldDescentWitness
      (semanticFieldFamily PL) (semanticFieldFamily PR)
      (semanticFieldFamily PG) glue := by
  refine { descend := ?_ }
  intro field l r hl hr
  cases field with
  | sourceReachability =>
      exact hglue.sourceBacked l r hl hr
  | authorityMonotonicity =>
      exact hglue.authoritySafe l r hl hr
  | graphConfluence =>
      exact hglue.graphConfluent l r hl hr
  | gaugeInvariance =>
      exact hglue.gaugeNonleaking l r hl hr
  | contractionCertification =>
      exact hglue.contractionSafe l r hl hr
  | omegaGluing =>
      exact hglue.omegaConsistent l r hl hr
  | freshnessValidity =>
      exact hglue.freshnessSafe l r hl hr

/-- THEOREM 6: P17's `C_safe` gluing theorem is the semantic-field descent
theorem read through Proposition 57. -/
theorem cSafe_gluing_via_field_descent
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (hglue : CSafeGluingWitness PL PR PG glue) :
    forall l r,
      CSafe PL l -> CSafe PR r -> CSafe PG (glue l r) := by
  intro l r hl hr
  exact (semanticFieldConvergence_iff_csafe PG (glue l r)).mp
    (fieldConvergence_preserved_by_descent
      (semanticFieldFamily PL) (semanticFieldFamily PR)
      (semanticFieldFamily PG) glue
      (cSafeGluingWitness_to_fieldDescent PL PR PG glue hglue)
      l r
      ((semanticFieldConvergence_iff_csafe PL l).mpr hl)
      ((semanticFieldConvergence_iff_csafe PR r).mpr hr))

/-- THEOREM 7: semantic field-boundary holonomy is exactly P17's
`GluingFailureSupport`. -/
theorem semanticFieldBoundaryHolonomy_iff_gluingFailureSupport
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (field : SemanticAtom) :
    FieldBoundaryHolonomy
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue l r field <->
      GluingFailureSupport PL PR PG glue l r field := by
  cases field <;> rfl

/-- THEOREM 8: with locally convergent/safe pieces, global `C_safe` failure is
exactly nonempty semantic field-boundary holonomy. -/
theorem semanticFieldBoundaryHolonomy_nonempty_iff_global_unsafe
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right)
    (hl : CSafe PL l) (hr : CSafe PR r) :
    (exists field,
      FieldBoundaryHolonomy
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue l r field) <->
      Not (CSafe PG (glue l r)) := by
  calc
    (exists field,
      FieldBoundaryHolonomy
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue l r field) <->
        Not (FieldConvergence (semanticFieldFamily PG) (glue l r)) :=
      fieldBoundaryHolonomy_nonempty_iff_local_convergent_global_failed
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue l r
        ((semanticFieldConvergence_iff_csafe PL l).mpr hl)
        ((semanticFieldConvergence_iff_csafe PR r).mpr hr)
    _ <-> Not (CSafe PG (glue l r)) :=
      not_congr (semanticFieldConvergence_iff_csafe PG (glue l r))

/-! ## Graph boundary holonomy -/

/-- THEOREM 9: the graph field's boundary holonomy is exactly the graph H¹
cross-critical-pair generator, once the runtime identifies the graph field with
the graph gluing cocycle. -/
theorem graph_fieldBoundaryHolonomy_iff_h1_generator
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
    FieldBoundaryHolonomy
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue l r SemanticAtom.graphConfluence <->
      GraphH1Generator C := by
  calc
    FieldBoundaryHolonomy
        (semanticFieldFamily PL) (semanticFieldFamily PR)
        (semanticFieldFamily PG) glue l r SemanticAtom.graphConfluence <->
        GluingFailureSupport PL PR PG glue l r
          SemanticAtom.graphConfluence :=
      semanticFieldBoundaryHolonomy_iff_gluingFailureSupport
        PL PR PG glue l r SemanticAtom.graphConfluence
    _ <-> GraphH1Generator C :=
      graph_gluing_failure_iff_h1_generator PL PR PG glue l r C hL hR hG

/-!
  Summary:
  - `FieldBoundaryHolonomy` is the generic Prop-valued descent obstruction:
    local field satisfaction survives on each side but fails after gluing.
  - For the seven AIppocampus fields, this is exactly the existing
    `GluingFailureSupport`.
  - The graph field's boundary holonomy is exactly the P17 H¹-like
    cross-critical-pair generator under the declared graph cocycle bridge.

  Remaining debt: arbitrary covers, restriction functor laws, sheaf descent,
  and actual cochain/cohomology objects are still future work.  This file only
  proves that the already-certified graph generator has the right field
  holonomy shape.
-/
