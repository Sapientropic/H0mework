/-
  Proposition 59: two-open field covers.

  Proposition 57 introduced Prop-valued field convergence.  Proposition 58
  introduced pairwise descent failure / boundary holonomy.  This file adds the
  next geometric layer: a two-open cover skeleton with restriction maps,
  overlap compatibility, compatible local pairs, and a descent certificate.

  This is still not full sheaf theory.  It is the smallest honest bridge from
  "a family of fields" to "local sections restrict, compatible local sections
  glue, and failure to glue is boundary holonomy".

  The semantic AIppocampus instance shows that P17's `CSafeRestrictionWitness`
  and `CSafeGluingWitness` are exactly restriction/descent data for the seven
  fields of P57/P58.
-/

import H0mework.Realization.Fields.Descent

/-! ## Field restrictions -/

/-- A restriction map preserves each field from a larger state space to a
local state space. -/
structure FieldRestrictionWitness {Global Local Field : Type*}
    (FG : FieldFamily Global Field) (FL : FieldFamily Local Field)
    (ρ : Global -> Local) where
  restrict :
    forall field x, FG.holds field x -> FL.holds field (ρ x)

/-- THEOREM 1: field convergence restricts along a field-preserving map. -/
theorem fieldConvergence_preserved_by_restriction
    {Global Local Field : Type*}
    (FG : FieldFamily Global Field) (FL : FieldFamily Local Field)
    (ρ : Global -> Local)
    (hρ : FieldRestrictionWitness FG FL ρ) :
    forall x, FieldConvergence FG x -> FieldConvergence FL (ρ x) := by
  intro x hx field
  exact hρ.restrict field x (hx field)

/-- The P17 `C_safe` restriction witness is the seven-field restriction witness
for the semantic field family. -/
theorem cSafeRestrictionWitness_to_fieldRestriction
    {Global Local : Type*}
    (PG : CSafePredicates Global) (PL : CSafePredicates Local)
    (ρ : Global -> Local)
    (hρ : CSafeRestrictionWitness PG PL ρ) :
    FieldRestrictionWitness (semanticFieldFamily PG) (semanticFieldFamily PL)
      ρ := by
  refine { restrict := ?_ }
  intro field x hx
  cases field with
  | sourceReachability =>
      exact hρ.sourceBacked x hx
  | authorityMonotonicity =>
      exact hρ.authoritySafe x hx
  | graphConfluence =>
      exact hρ.graphConfluent x hx
  | gaugeInvariance =>
      exact hρ.gaugeNonleaking x hx
  | contractionCertification =>
      exact hρ.contractionSafe x hx
  | omegaGluing =>
      exact hρ.omegaConsistent x hx
  | freshnessValidity =>
      exact hρ.freshnessSafe x hx

/-- THEOREM 2: P17's `C_safe` restriction theorem is the semantic-field
restriction theorem read through Proposition 57. -/
theorem cSafe_restriction_via_field_restriction
    {Global Local : Type*}
    (PG : CSafePredicates Global) (PL : CSafePredicates Local)
    (ρ : Global -> Local)
    (hρ : CSafeRestrictionWitness PG PL ρ) :
    forall x, CSafe PG x -> CSafe PL (ρ x) := by
  intro x hx
  exact (semanticFieldConvergence_iff_csafe PL (ρ x)).mp
    (fieldConvergence_preserved_by_restriction
      (semanticFieldFamily PG) (semanticFieldFamily PL) ρ
      (cSafeRestrictionWitness_to_fieldRestriction PG PL ρ hρ)
      x ((semanticFieldConvergence_iff_csafe PG x).mpr hx))

/-! ## Two-open covers -/

/-- A two-open cover skeleton for Prop-valued fields.  `Global` is covered by
`Left` and `Right`, and both local pieces restrict to `Overlap`. -/
structure TwoOpenFieldCover
    (Global Left Right Overlap Field : Type*) where
  FG : FieldFamily Global Field
  FL : FieldFamily Left Field
  FR : FieldFamily Right Field
  FO : FieldFamily Overlap Field
  toLeft : Global -> Left
  toRight : Global -> Right
  leftToOverlap : Left -> Overlap
  rightToOverlap : Right -> Overlap
  glue : Left -> Right -> Global

/-- A pair of local sections is overlap-compatible when their restrictions to
the overlap satisfy the same fields. -/
def FieldOverlapCompatible
    {Global Left Right Overlap Field : Type*}
    (C : TwoOpenFieldCover Global Left Right Overlap Field)
    (l : Left) (r : Right) : Prop :=
  forall field,
    C.FO.holds field (C.leftToOverlap l) <->
      C.FO.holds field (C.rightToOverlap r)

/-- A local pair carries the compatibility proof that a sheaf-style gluing
attempt is allowed. -/
structure CompatibleLocalPair
    {Global Left Right Overlap Field : Type*}
    (C : TwoOpenFieldCover Global Left Right Overlap Field) where
  left : Left
  right : Right
  compatible : FieldOverlapCompatible C left right

/-- The local pair converges when both of its local sections converge. -/
def CompatibleLocalPair.Converges
    {Global Left Right Overlap Field : Type*}
    {C : TwoOpenFieldCover Global Left Right Overlap Field}
    (p : CompatibleLocalPair C) : Prop :=
  FieldConvergence C.FL p.left /\ FieldConvergence C.FR p.right

/-- A descent certificate for a two-open field cover: global sections restrict
to both opens, local sections restrict to the overlap, and local convergence
descends across the glue map. -/
structure TwoOpenFieldDescentCertificate
    {Global Left Right Overlap Field : Type*}
    (C : TwoOpenFieldCover Global Left Right Overlap Field) where
  restrictLeft :
    FieldRestrictionWitness C.FG C.FL C.toLeft
  restrictRight :
    FieldRestrictionWitness C.FG C.FR C.toRight
  restrictLeftOverlap :
    FieldRestrictionWitness C.FL C.FO C.leftToOverlap
  restrictRightOverlap :
    FieldRestrictionWitness C.FR C.FO C.rightToOverlap
  descend :
    FieldDescentWitness C.FL C.FR C.FG C.glue

/-- THEOREM 3: a global convergent section restricts to convergent local
sections on the cover. -/
theorem global_convergence_restricts_to_cover
    {Global Left Right Overlap Field : Type*}
    {C : TwoOpenFieldCover Global Left Right Overlap Field}
    (D : TwoOpenFieldDescentCertificate C) :
    forall x,
      FieldConvergence C.FG x ->
      FieldConvergence C.FL (C.toLeft x) /\
        FieldConvergence C.FR (C.toRight x) := by
  intro x hx
  exact ⟨
    fieldConvergence_preserved_by_restriction
      C.FG C.FL C.toLeft D.restrictLeft x hx,
    fieldConvergence_preserved_by_restriction
      C.FG C.FR C.toRight D.restrictRight x hx
  ⟩

/-- THEOREM 4: the restrictions of a global convergent section are compatible
on the overlap. -/
theorem global_convergence_gives_overlap_compatibility
    {Global Left Right Overlap Field : Type*}
    {C : TwoOpenFieldCover Global Left Right Overlap Field}
    (D : TwoOpenFieldDescentCertificate C) :
    forall x,
      FieldConvergence C.FG x ->
      FieldOverlapCompatible C (C.toLeft x) (C.toRight x) := by
  intro x hx field
  have hL :
      FieldConvergence C.FL (C.toLeft x) :=
    fieldConvergence_preserved_by_restriction
      C.FG C.FL C.toLeft D.restrictLeft x hx
  have hR :
      FieldConvergence C.FR (C.toRight x) :=
    fieldConvergence_preserved_by_restriction
      C.FG C.FR C.toRight D.restrictRight x hx
  have hOL :
      C.FO.holds field (C.leftToOverlap (C.toLeft x)) :=
    fieldConvergence_preserved_by_restriction
      C.FL C.FO C.leftToOverlap D.restrictLeftOverlap
      (C.toLeft x) hL field
  have hOR :
      C.FO.holds field (C.rightToOverlap (C.toRight x)) :=
    fieldConvergence_preserved_by_restriction
      C.FR C.FO C.rightToOverlap D.restrictRightOverlap
      (C.toRight x) hR field
  exact ⟨fun _ => hOR, fun _ => hOL⟩

/-- THEOREM 5: compatible local convergence descends to global convergence.
At this Prop-valued level, compatibility is carried by the local-pair object;
the actual convergence proof uses the descent witness. -/
theorem compatible_local_convergence_descends
    {Global Left Right Overlap Field : Type*}
    {C : TwoOpenFieldCover Global Left Right Overlap Field}
    (D : TwoOpenFieldDescentCertificate C) :
    forall p : CompatibleLocalPair C,
      p.Converges ->
      FieldConvergence C.FG (C.glue p.left p.right) := by
  intro p hp
  exact fieldConvergence_preserved_by_descent
    C.FL C.FR C.FG C.glue D.descend p.left p.right hp.1 hp.2

/-- Cover-level boundary holonomy is the P58 boundary holonomy, now attached to
a compatible local pair in a two-open cover. -/
def CoverBoundaryHolonomy
    {Global Left Right Overlap Field : Type*}
    (C : TwoOpenFieldCover Global Left Right Overlap Field)
    (p : CompatibleLocalPair C) (field : Field) : Prop :=
  FieldBoundaryHolonomy C.FL C.FR C.FG C.glue p.left p.right field

/-- THEOREM 6: for a compatible local pair whose local sections converge,
failure of the glued global section is exactly nonempty cover-boundary
holonomy. -/
theorem coverBoundaryHolonomy_nonempty_iff_global_failed
    {Global Left Right Overlap Field : Type*}
    {C : TwoOpenFieldCover Global Left Right Overlap Field}
    (p : CompatibleLocalPair C)
    (hp : p.Converges) :
    (exists field, CoverBoundaryHolonomy C p field) <->
      Not (FieldConvergence C.FG (C.glue p.left p.right)) := by
  exact fieldBoundaryHolonomy_nonempty_iff_local_convergent_global_failed
    C.FL C.FR C.FG C.glue p.left p.right hp.1 hp.2

/-- THEOREM 7: a descent certificate rules out cover-boundary holonomy. -/
theorem no_coverBoundaryHolonomy_of_descent
    {Global Left Right Overlap Field : Type*}
    {C : TwoOpenFieldCover Global Left Right Overlap Field}
    (D : TwoOpenFieldDescentCertificate C) :
    forall p field, Not (CoverBoundaryHolonomy C p field) := by
  intro p field
  exact no_fieldBoundaryHolonomy_of_descent
    C.FL C.FR C.FG C.glue D.descend p.left p.right field

/-! ## Semantic two-open covers -/

/-- Package AIppocampus `CSafePredicates` as a two-open semantic field cover. -/
def semanticTwoOpenFieldCover
    {Global Left Right Overlap : Type*}
    (PG : CSafePredicates Global)
    (PL : CSafePredicates Left)
    (PR : CSafePredicates Right)
    (PO : CSafePredicates Overlap)
    (toLeft : Global -> Left)
    (toRight : Global -> Right)
    (leftToOverlap : Left -> Overlap)
    (rightToOverlap : Right -> Overlap)
    (glue : Left -> Right -> Global) :
    TwoOpenFieldCover Global Left Right Overlap SemanticAtom where
  FG := semanticFieldFamily PG
  FL := semanticFieldFamily PL
  FR := semanticFieldFamily PR
  FO := semanticFieldFamily PO
  toLeft := toLeft
  toRight := toRight
  leftToOverlap := leftToOverlap
  rightToOverlap := rightToOverlap
  glue := glue

/-- THEOREM 8: AIppocampus restriction/gluing witnesses instantiate the
two-open descent certificate for the seven semantic fields. -/
theorem semanticTwoOpenFieldDescentCertificate
    {Global Left Right Overlap : Type*}
    (PG : CSafePredicates Global)
    (PL : CSafePredicates Left)
    (PR : CSafePredicates Right)
    (PO : CSafePredicates Overlap)
    (toLeft : Global -> Left)
    (toRight : Global -> Right)
    (leftToOverlap : Left -> Overlap)
    (rightToOverlap : Right -> Overlap)
    (glue : Left -> Right -> Global)
    (hL : CSafeRestrictionWitness PG PL toLeft)
    (hR : CSafeRestrictionWitness PG PR toRight)
    (hOL : CSafeRestrictionWitness PL PO leftToOverlap)
    (hOR : CSafeRestrictionWitness PR PO rightToOverlap)
    (hglue : CSafeGluingWitness PL PR PG glue) :
    TwoOpenFieldDescentCertificate
      (semanticTwoOpenFieldCover PG PL PR PO
        toLeft toRight leftToOverlap rightToOverlap glue) := by
  refine {
    restrictLeft := ?_,
    restrictRight := ?_,
    restrictLeftOverlap := ?_,
    restrictRightOverlap := ?_,
    descend := ?_
  }
  · exact cSafeRestrictionWitness_to_fieldRestriction PG PL toLeft hL
  · exact cSafeRestrictionWitness_to_fieldRestriction PG PR toRight hR
  · exact cSafeRestrictionWitness_to_fieldRestriction PL PO leftToOverlap hOL
  · exact cSafeRestrictionWitness_to_fieldRestriction PR PO rightToOverlap hOR
  · exact cSafeGluingWitness_to_fieldDescent PL PR PG glue hglue

/-!
  Summary:
  - `TwoOpenFieldCover` is the first explicit local/global geometry for the
    memory fields: global sections restrict to left/right opens, both restrict
    to an overlap, compatible local pairs can be glued, and failures to glue
    are cover-boundary holonomy.
  - P17's `CSafeRestrictionWitness` and `CSafeGluingWitness` instantiate this
    cover geometry for the seven AIppocampus fields.

  Remaining debt: this is still a two-open, Prop-valued skeleton.  The next
  steps are arbitrary finite covers, functorial restriction laws, and then a
  genuine cochain/cohomology quotient for global gluing obstructions.
-/
