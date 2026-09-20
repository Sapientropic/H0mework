/-
  Proposition 105: projection-visible completeness for structure-determined
  obligations.

  Proposition 104 proved that, once a system is formalized as a P94
  semantic-memory pullback, the discovery table is forced by structure.  This
  file pushes the same idea to the obligation vocabulary itself.

  The key move is to stop treating "safety-relevant predicates" as an external
  checklist.  For a structure-determined seven-facet system, the canonical
  visible predicates are exactly those that factor through the semantic Boolean
  projection.  On that domain, the seven facets are complete: every
  projection-visible predicate is expressible by the Boolean query algebra over
  the seven semantic atoms.

  Boundary: this still does not prove that the informal AIppocampus slogan
  `reflexive + source-backed + navigation-only` uniquely generates the P94
  projection.  It proves the next formal step: once the projection is the
  system structure, the obligation semantics and finite query vocabulary are
  uniquely determined by it.
-/

import H0mework.Realization.Reflexive.TruthTable
import H0mework.Realization.QuerySupport.P104

/-! ## Obligations pulled back from a semantic projection -/

/-- Pull back the concrete seven-axis Boolean semantic semantics along a
projection into `SemanticBoolState`. -/
def obligationsFromSemanticProjection {State : Type*}
    (project : State -> SemanticBoolState) :
    ObligationSemantics State SemanticAtom where
  holds := fun a x =>
    (semanticObligationSemantics semanticBoolPredicates).holds a (project x)

namespace StructureDeterminedSevenFacetSystem

variable {State : Type*}

/-- THEOREM 1: the obligations of a structure-determined seven-facet system are
exactly the pullback of its semantic Boolean projection. -/
theorem obligations_eq_projection_pullback
    (S : StructureDeterminedSevenFacetSystem State)
    (x : State) (a : SemanticAtom) :
    S.obligations.holds a x <->
      (obligationsFromSemanticProjection
        S.pullback.projection.project).holds a x :=
  S.pullback.projection.atom_iff x a

/-- THEOREM 2: any other obligation semantics compatible with the same
projection is extensionally equal to the system obligations. -/
theorem obligations_unique_from_projection
    (S : StructureDeterminedSevenFacetSystem State)
    (Other : ObligationSemantics State SemanticAtom)
    (hOther :
      forall x a,
        Other.holds a x <->
          (obligationsFromSemanticProjection
            S.pullback.projection.project).holds a x)
    (x : State) (a : SemanticAtom) :
    Other.holds a x <-> S.obligations.holds a x :=
  (hOther x a).trans (S.obligations_eq_projection_pullback x a).symm

/-! ## Atom equivalence is exactly projection equality -/

/-- Boolean states are equal when every semantic atom reads the same Boolean
value. -/
theorem semanticBoolState_eq_of_values
    {x y : SemanticBoolState}
    (h : forall a, semanticBoolValue x a = semanticBoolValue y a) :
    x = y := by
  cases x with
  | mk xs xa xg xga xc xo xf =>
      cases y with
      | mk ys ya yg yga yc yo yf =>
          have hs := h SemanticAtom.sourceReachability
          have ha := h SemanticAtom.authorityMonotonicity
          have hg := h SemanticAtom.graphConfluence
          have hga := h SemanticAtom.gaugeInvariance
          have hc := h SemanticAtom.contractionCertification
          have ho := h SemanticAtom.omegaGluing
          have hf := h SemanticAtom.freshnessValidity
          simp [semanticBoolValue] at hs ha hg hga hc ho hf
          subst ys
          subst ya
          subst yg
          subst yga
          subst yc
          subst yo
          subst yf
          rfl

/-- A Boolean is determined by whether it is true. -/
theorem bool_eq_of_true_iff {b c : Bool}
    (h : (b = true) <-> (c = true)) :
    b = c := by
  cases b <;> cases c <;> simp at h ⊢

/-- THEOREM 3: atom-equivalent states have the same semantic projection. -/
theorem projection_eq_of_atomEquiv
    (S : StructureDeterminedSevenFacetSystem State)
    {x y : State}
    (hxy : AtomEquiv S.obligations x y) :
    S.pullback.projection.project x = S.pullback.projection.project y := by
  apply semanticBoolState_eq_of_values
  intro a
  apply bool_eq_of_true_iff
  calc
    semanticBoolValue (S.pullback.projection.project x) a = true <->
        (semanticObligationSemantics semanticBoolPredicates).holds a
          (S.pullback.projection.project x) :=
      (semanticBoolHolds_iff_value (S.pullback.projection.project x) a).symm
    _ <-> S.obligations.holds a x :=
      (S.pullback.projection.atom_iff x a).symm
    _ <-> S.obligations.holds a y :=
      hxy a
    _ <-> (semanticObligationSemantics semanticBoolPredicates).holds a
          (S.pullback.projection.project y) :=
      S.pullback.projection.atom_iff y a
    _ <-> semanticBoolValue (S.pullback.projection.project y) a = true :=
      semanticBoolHolds_iff_value (S.pullback.projection.project y) a

/-- THEOREM 4: equal semantic projections imply atom-equivalence. -/
theorem atomEquiv_of_projection_eq
    (S : StructureDeterminedSevenFacetSystem State)
    {x y : State}
    (hproj :
      S.pullback.projection.project x = S.pullback.projection.project y) :
    AtomEquiv S.obligations x y := by
  intro a
  calc
    S.obligations.holds a x <->
        (semanticObligationSemantics semanticBoolPredicates).holds a
          (S.pullback.projection.project x) :=
      S.pullback.projection.atom_iff x a
    _ <-> (semanticObligationSemantics semanticBoolPredicates).holds a
          (S.pullback.projection.project y) := by
      rw [hproj]
    _ <-> S.obligations.holds a y :=
      (S.pullback.projection.atom_iff y a).symm

/-- THEOREM 5: atom-equivalence is exactly equality of semantic projections. -/
theorem atomEquiv_iff_projection_eq
    (S : StructureDeterminedSevenFacetSystem State)
    (x y : State) :
    AtomEquiv S.obligations x y <->
      S.pullback.projection.project x = S.pullback.projection.project y := by
  constructor
  · exact S.projection_eq_of_atomEquiv
  · exact S.atomEquiv_of_projection_eq

/-! ## Completeness for projection-visible predicates -/

/-- A predicate is projection-visible when it cannot distinguish states with
the same semantic Boolean projection. -/
def ProjectionVisible
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop) : Prop :=
  forall {x y},
    S.pullback.projection.project x = S.pullback.projection.project y ->
      (target x <-> target y)

/-- THEOREM 6: projection-visible predicates have an atom-coverage certificate.
-/
theorem projectionVisible_atomCoverage
    (S : StructureDeterminedSevenFacetSystem State) :
    AtomCoverageCertificate S.obligations (ProjectionVisible S) where
  invariant := by
    intro target hvisible x y hxy
    exact hvisible (S.projection_eq_of_atomEquiv hxy)

/-- THEOREM 7: every projection-visible predicate is expressible by the Boolean
query algebra over the seven semantic atoms. -/
theorem projectionVisible_queryExpressible
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop)
    (hvisible : ProjectionVisible S target) :
    QueryExpressible S.obligations target := by
  classical
  exact
    (finite_queryExpressible_iff_atomInvariant S.obligations target).mpr
      (by
        intro x y hxy
        exact hvisible (S.projection_eq_of_atomEquiv hxy))

/-- THEOREM 8: the seven facets are complete for the structurally generated
family of projection-visible predicates. -/
theorem projectionVisible_facetComplete
    (S : StructureDeterminedSevenFacetSystem State) :
    FiniteFacetCompleteFor S.obligations (ProjectionVisible S) := by
  intro target hvisible
  exact S.projectionVisible_queryExpressible target hvisible

/-- THEOREM 9: a predicate that is not projection-visible is outside the
structurally generated obligation vocabulary.  This is the exact failure mode
for a proposed "eighth facet": it must distinguish states that the system
projection intentionally identifies. -/
theorem not_projectionVisible_of_separating_projection_equal
    (S : StructureDeterminedSevenFacetSystem State)
    (target : State -> Prop)
    {x y : State}
    (hproj :
      S.pullback.projection.project x = S.pullback.projection.project y)
    (hsep : target x ∧ ¬ target y) :
    Not (ProjectionVisible S target) := by
  intro hvisible
  exact hsep.2 ((hvisible hproj).mp hsep.1)

end StructureDeterminedSevenFacetSystem

/-!
  Summary:
  - Given a P94/P104 structure, obligation semantics is the unique pullback of
    the semantic Boolean projection.
  - Atom equivalence is exactly equality of that projection.
  - Therefore the seven facets are complete for the structurally generated
    family of projection-visible predicates, without appealing to an external
    checklist.
  - The remaining upstream debt is unchanged and now sharper: prove that the
    intended AIppocampus primitives uniquely supply this projection, or exhibit
    a separating predicate as an honest eighth-facet candidate.
-/
