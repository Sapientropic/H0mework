/-
  Proposition 60: indexed field covers.

  Proposition 59 gave a two-open cover skeleton.  This file removes the
  two-open special case: an indexed field cover has an arbitrary family of
  local state spaces, pairwise overlaps, restriction maps, and a glue operation
  for a compatible family of local sections.

  This is still not a full topological sheaf.  It does not assert that the
  index family is a genuine open cover of a topological space, and it does not
  build cochains.  It does prove the cover-level geometric laws that the memory
  language needs next:

    * global convergence restricts to every local section;
    * global convergence makes all pairwise overlap restrictions compatible;
    * compatible locally convergent families descend when a descent
      certificate is supplied;
    * failure of a locally convergent family to glue is exactly nonempty
      indexed boundary holonomy.
-/

import H0mework.Realization.Fields.Restriction

/-! ## Indexed covers -/

/-- An indexed field cover skeleton.  `Local i` is the state space for one
local open, and `Overlap i j` is the state space for the overlap of two locals.
-/
structure IndexedFieldCover
    (Index : Type*) (Global : Type*) (Local : Index -> Type*)
    (Overlap : Index -> Index -> Type*) (Field : Type*) where
  FG : FieldFamily Global Field
  FL : forall i, FieldFamily (Local i) Field
  FO : forall i j, FieldFamily (Overlap i j) Field
  toLocal : forall i, Global -> Local i
  leftToOverlap : forall i j, Local i -> Overlap i j
  rightToOverlap : forall i j, Local j -> Overlap i j
  glue : (forall i, Local i) -> Global

/-- A family of local sections over an indexed cover. -/
abbrev LocalSectionFamily
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (_C : IndexedFieldCover Index Global Local Overlap Field) :=
  forall i, Local i

/-- Pairwise overlap compatibility for an indexed family of local sections. -/
def IndexedOverlapCompatible
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : IndexedFieldCover Index Global Local Overlap Field)
    (s : LocalSectionFamily C) : Prop :=
  forall i j field,
    (C.FO i j).holds field (C.leftToOverlap i j (s i)) <->
      (C.FO i j).holds field (C.rightToOverlap i j (s j))

/-- A compatible local family carries the pairwise overlap proof. -/
structure CompatibleIndexedLocalFamily
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : IndexedFieldCover Index Global Local Overlap Field) where
  sections : LocalSectionFamily C
  compatible : IndexedOverlapCompatible C sections

/-- A compatible indexed local family is locally convergent when every local
component converges. -/
def CompatibleIndexedLocalFamily.Converges
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {C : IndexedFieldCover Index Global Local Overlap Field}
    (p : CompatibleIndexedLocalFamily C) : Prop :=
  forall i, FieldConvergence (C.FL i) (p.sections i)

/-- An indexed descent certificate: global sections restrict to locals, locals
restrict to pairwise overlaps, and locally convergent families glue globally.
-/
structure IndexedFieldDescentCertificate
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : IndexedFieldCover Index Global Local Overlap Field) where
  restrictLocal :
    forall i, FieldRestrictionWitness C.FG (C.FL i) (C.toLocal i)
  restrictLeftOverlap :
    forall i j,
      FieldRestrictionWitness (C.FL i) (C.FO i j) (C.leftToOverlap i j)
  restrictRightOverlap :
    forall i j,
      FieldRestrictionWitness (C.FL j) (C.FO i j) (C.rightToOverlap i j)
  descend :
    forall s : LocalSectionFamily C,
      (forall i, FieldConvergence (C.FL i) (s i)) ->
      FieldConvergence C.FG (C.glue s)

/-- THEOREM 1: global convergence restricts to every member of the indexed
cover. -/
theorem indexed_global_convergence_restricts
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {C : IndexedFieldCover Index Global Local Overlap Field}
    (D : IndexedFieldDescentCertificate C) :
    forall x i,
      FieldConvergence C.FG x ->
      FieldConvergence (C.FL i) (C.toLocal i x) := by
  intro x i hx
  exact fieldConvergence_preserved_by_restriction
    C.FG (C.FL i) (C.toLocal i) (D.restrictLocal i) x hx

/-- THEOREM 2: global convergence makes all pairwise overlap restrictions
compatible. -/
theorem indexed_global_convergence_gives_overlap_compatibility
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {C : IndexedFieldCover Index Global Local Overlap Field}
    (D : IndexedFieldDescentCertificate C) :
    forall x,
      FieldConvergence C.FG x ->
      IndexedOverlapCompatible C (fun i => C.toLocal i x) := by
  intro x hx i j field
  have hLi :
      FieldConvergence (C.FL i) (C.toLocal i x) :=
    indexed_global_convergence_restricts D x i hx
  have hLj :
      FieldConvergence (C.FL j) (C.toLocal j x) :=
    indexed_global_convergence_restricts D x j hx
  have hOi :
      (C.FO i j).holds field
        (C.leftToOverlap i j (C.toLocal i x)) :=
    fieldConvergence_preserved_by_restriction
      (C.FL i) (C.FO i j) (C.leftToOverlap i j)
      (D.restrictLeftOverlap i j) (C.toLocal i x) hLi field
  have hOj :
      (C.FO i j).holds field
        (C.rightToOverlap i j (C.toLocal j x)) :=
    fieldConvergence_preserved_by_restriction
      (C.FL j) (C.FO i j) (C.rightToOverlap i j)
      (D.restrictRightOverlap i j) (C.toLocal j x) hLj field
  exact ⟨fun _ => hOj, fun _ => hOi⟩

/-- THEOREM 3: a compatible locally convergent indexed family descends to a
globally convergent glued section. -/
theorem compatible_indexed_local_convergence_descends
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {C : IndexedFieldCover Index Global Local Overlap Field}
    (D : IndexedFieldDescentCertificate C) :
    forall p : CompatibleIndexedLocalFamily C,
      p.Converges ->
      FieldConvergence C.FG (C.glue p.sections) := by
  intro p hp
  exact D.descend p.sections hp

/-- Indexed cover-boundary holonomy: every local component satisfies a field,
but the glued global section fails that field. -/
def IndexedCoverBoundaryHolonomy
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : IndexedFieldCover Index Global Local Overlap Field)
    (s : LocalSectionFamily C) (field : Field) : Prop :=
  (forall i, (C.FL i).holds field (s i)) /\
    Not (C.FG.holds field (C.glue s))

/-- THEOREM 4: for a locally convergent indexed family, failure of the glued
global section is exactly nonempty indexed boundary holonomy. -/
theorem indexedCoverBoundaryHolonomy_nonempty_iff_global_failed
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    (C : IndexedFieldCover Index Global Local Overlap Field)
    (s : LocalSectionFamily C)
    (hlocal : forall i, FieldConvergence (C.FL i) (s i)) :
    (exists field, IndexedCoverBoundaryHolonomy C s field) <->
      Not (FieldConvergence C.FG (C.glue s)) := by
  constructor
  · rintro ⟨field, _hloc, hfail⟩ hglobal
    exact hfail (hglobal field)
  · intro hnot
    rcases (fieldFailure_nonempty_iff_not_convergent C.FG (C.glue s)).mpr
      hnot with ⟨field, hfail⟩
    exact ⟨field, (fun i => hlocal i field), hfail⟩

/-- THEOREM 5: an indexed descent certificate rules out indexed boundary
holonomy for locally convergent families. -/
theorem no_indexedCoverBoundaryHolonomy_of_descent
    {Index : Type*} {Global : Type*} {Local : Index -> Type*}
    {Overlap : Index -> Index -> Type*} {Field : Type*}
    {C : IndexedFieldCover Index Global Local Overlap Field}
    (D : IndexedFieldDescentCertificate C) :
    forall s : LocalSectionFamily C,
      (forall i, FieldConvergence (C.FL i) (s i)) ->
      forall field, Not (IndexedCoverBoundaryHolonomy C s field) := by
  intro s hlocal field hhol
  have hglobal : FieldConvergence C.FG (C.glue s) :=
    D.descend s hlocal
  exact hhol.2 (hglobal field)

/-!
  Summary:
  - `IndexedFieldCover` generalizes Proposition 59's two-open cover skeleton
    to arbitrary indexed local families with pairwise overlaps.
  - A descent certificate gives the expected sheaf-like direction:
    global-to-local restriction, overlap compatibility, and
    compatible-local-to-global descent.
  - Indexed boundary holonomy is the canonical field that all local components
    satisfy but the glued global state fails.

  Remaining debt: the index family is still abstract cover data, not a
  topological site; compatibility is Prop-valued field agreement, not section
  equality; and no cochain quotient / `δ² = 0` theorem has been constructed.
-/
