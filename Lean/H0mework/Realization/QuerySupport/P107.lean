/-
  Proposition 107: eighth-facet candidates are either already expressible or
  projection-refining.

  Proposition 105 proved the positive half: every projection-visible predicate
  is expressible by the Boolean query algebra over the seven semantic atoms.
  Proposition 23 had already proved the generic negative half: generated
  Boolean queries cannot distinguish atom-equivalent states.

  This file closes that loop for structure-determined seven-facet systems:

      QueryExpressible  <->  ProjectionVisible.

  Therefore a proposed "eighth facet" has only two formal statuses:

    * it is projection-visible, hence already expressible by the seven-facet
      query language; or
    * it separates two states with the same semantic projection, hence it is
      not a missing checklist item but a demand to refine the system structure.

  This is the precise P94/P105 boundary behind the informal claim that, once
  the system structure is fixed, the obligation vocabulary is a function of
  that structure rather than an externally chosen list.

  Boundary: this still does not prove that the slogan `reflexive +
  source-backed + navigation-only` uniquely generates the P94 projection.  It
  proves that after a P94/P105 projection is supplied, the "missing eighth
  facet" question has a canonical answer.
-/

import H0mework.Realization.QueryPlans.P106

namespace StructureDeterminedSevenFacetSystem

variable {State : Type*}

/-! ## Same projection, same obligation language -/

/-- THEOREM 1: two structure-determined systems with the same semantic
projection have extensionally equal obligation semantics. -/
theorem obligations_extensional_of_projection_eq
    (S T : StructureDeterminedSevenFacetSystem State)
    (hproj :
      forall x,
        S.pullback.projection.project x =
          T.pullback.projection.project x)
    (x : State) (a : SemanticAtom) :
    S.obligations.holds a x <-> T.obligations.holds a x := by
  calc
    S.obligations.holds a x <->
        (semanticObligationSemantics semanticBoolPredicates).holds a
          (S.pullback.projection.project x) :=
      S.pullback.projection.atom_iff x a
    _ <->
        (semanticObligationSemantics semanticBoolPredicates).holds a
          (T.pullback.projection.project x) := by
      rw [hproj x]
    _ <-> T.obligations.holds a x :=
      (T.pullback.projection.atom_iff x a).symm

/-- THEOREM 2: projection-visible predicate families are determined by the
semantic projection, not by an independent interpretation of the facet list. -/
theorem projectionVisible_iff_of_projection_eq
    (S T : StructureDeterminedSevenFacetSystem State)
    (hproj :
      forall x,
        S.pullback.projection.project x =
          T.pullback.projection.project x)
    (target : State -> Prop) :
    ProjectionVisible S target <-> ProjectionVisible T target := by
  constructor
  · intro hS x y hTxy
    apply hS
    calc
      S.pullback.projection.project x =
          T.pullback.projection.project x := hproj x
      _ = T.pullback.projection.project y := hTxy
      _ = S.pullback.projection.project y := (hproj y).symm
  · intro hT x y hSxy
    apply hT
    calc
      T.pullback.projection.project x =
          S.pullback.projection.project x := (hproj x).symm
      _ = S.pullback.projection.project y := hSxy
      _ = T.pullback.projection.project y := hproj y

/-! ## Exact expressibility boundary -/

/-- THEOREM 3: in a structure-determined seven-facet system, Boolean query
expressibility is exactly projection visibility. -/
theorem queryExpressible_iff_projectionVisible
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop) :
    QueryExpressible S.obligations target <-> ProjectionVisible S target := by
  constructor
  · intro hexpr x y hproj
    exact queryExpressible_invariant S.obligations hexpr
      (S.atomEquiv_of_projection_eq hproj)
  · intro hvisible
    exact S.projectionVisible_queryExpressible target hvisible

/-- A candidate facet refines the current projection when it distinguishes two
states that the current seven-axis projection identifies. -/
def ProjectionRefiningCandidate
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop) : Prop :=
  exists x y,
    S.pullback.projection.project x =
      S.pullback.projection.project y /\
    ((target x /\ ¬ target y) \/ (¬ target x /\ target y))

/-- THEOREM 4: failing projection visibility is exactly being a
projection-refining candidate. -/
theorem not_projectionVisible_iff_projectionRefining
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop) :
    ¬ ProjectionVisible S target <->
      ProjectionRefiningCandidate S target := by
  classical
  constructor
  · intro hnot
    unfold ProjectionVisible at hnot
    unfold ProjectionRefiningCandidate
    push Not at hnot
    exact hnot
  · rintro ⟨x, y, hproj, hsep⟩ hvisible
    have hiff := hvisible hproj
    rcases hsep with hxy | hyx
    · exact hxy.2 (hiff.mp hxy.1)
    · exact hyx.1 (hiff.mpr hyx.2)

/-- THEOREM 5: a candidate predicate is inexpressible by the seven-facet query
language exactly when it refines the current projection. -/
theorem not_queryExpressible_iff_projectionRefining
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop) :
    ¬ QueryExpressible S.obligations target <->
      ProjectionRefiningCandidate S target := by
  rw [S.queryExpressible_iff_projectionVisible target,
    S.not_projectionVisible_iff_projectionRefining target]

/-- THEOREM 6: every candidate facet either compiles into the existing
seven-facet query language or gives a concrete same-projection/separating-state
witness that the system projection must be refined. -/
theorem candidateFacet_query_or_projectionRefining
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop) :
    QueryExpressible S.obligations target \/
      ProjectionRefiningCandidate S target := by
  classical
  by_cases hexpr : QueryExpressible S.obligations target
  · exact Or.inl hexpr
  · exact Or.inr
      ((S.not_queryExpressible_iff_projectionRefining target).mp hexpr)

/-- THEOREM 7: if two structure-determined systems have the same projection,
they agree on which candidate predicates are expressible by the generated
obligation query language. -/
theorem queryExpressible_iff_of_projection_eq
    (S T : StructureDeterminedSevenFacetSystem State)
    (hproj :
      forall x,
        S.pullback.projection.project x =
          T.pullback.projection.project x)
    (target : State -> Prop) :
    QueryExpressible S.obligations target <->
      QueryExpressible T.obligations target := by
  calc
    QueryExpressible S.obligations target <->
        ProjectionVisible S target :=
      S.queryExpressible_iff_projectionVisible target
    _ <-> ProjectionVisible T target :=
      S.projectionVisible_iff_of_projection_eq T hproj target
    _ <-> QueryExpressible T.obligations target :=
      (T.queryExpressible_iff_projectionVisible target).symm

/-!
  Summary:
  - Same projection means same obligation semantics and same projection-visible
    predicate family.
  - In a structure-determined seven-facet system,
    `QueryExpressible <-> ProjectionVisible`.
  - Therefore an alleged eighth facet is either already generated by the
    seven-facet query language or it is a projection-refining signal.  It is
    not an ambiguous missing checklist item.

  Remaining boundary:
  - The upstream theorem is still open: prove that the intended AIppocampus
    primitives uniquely generate the P94/P105 semantic projection.  P107 says
    that once that projection is fixed, the downstream obligation/query
    vocabulary has no additional interpretive freedom.
-/


end StructureDeterminedSevenFacetSystem
