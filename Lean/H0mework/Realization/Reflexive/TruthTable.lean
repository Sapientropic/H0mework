/-
  Proposition 42: finite facet completeness is exactly atom coverage.

  Proposition 23 proved the negative half:

    every generated Boolean query is invariant under atom-equivalence.

  This file proves the finite converse.  When the primitive atom vocabulary is
  finite, every atom-equivalence-invariant predicate is expressible by a finite
  disjunction of truth-table minterms.  Therefore a finite facet set is complete
  for a family of safety-relevant predicates exactly when every predicate in
  that family is invariant under the facet-induced equivalence relation.

  This is the honest mathematical shape of the "are the seven facets complete?"
  question.  Completeness is not asserted for free; it is reduced to a coverage
  certificate that no safety-relevant predicate can see a distinction invisible
  to the chosen facets.
-/

import H0mework.Realization.Observation.AtomEquivalence

/-! ## Truth-table queries over finite atom vocabularies -/

/-- A state matches an atom truth assignment when every atom has exactly the
assigned truth value. -/
def AssignmentMatches {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (assignment : Atom -> Bool) (x : State) : Prop :=
  forall a, S.holds a x <-> assignment a = true

/-- A literal query for one atom under a truth assignment. -/
def literalQuery {Atom : Type*} (a : Atom) (truth : Bool) :
    BoolQuery Atom :=
  if truth then BoolQuery.atom a else BoolQuery.neg (BoolQuery.atom a)

/-- A minterm query from an explicit finite atom list. -/
def mintermFromList {Atom : Type*} :
    List Atom -> (Atom -> Bool) -> BoolQuery Atom
  | [], _assignment => BoolQuery.top
  | a :: rest, assignment =>
      BoolQuery.meet (literalQuery a (assignment a))
        (mintermFromList rest assignment)

theorem literalQuery_eval_iff {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (a : Atom) (truth : Bool) (x : State) :
    BoolQuery.eval S (literalQuery a truth) x <->
      (S.holds a x <-> truth = true) := by
  cases truth <;> simp [literalQuery, BoolQuery.eval]

theorem mintermFromList_eval_iff {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (atoms : List Atom) (assignment : Atom -> Bool) (x : State) :
    BoolQuery.eval S (mintermFromList atoms assignment) x <->
      forall a, a ∈ atoms -> (S.holds a x <-> assignment a = true) := by
  induction atoms with
  | nil =>
      simp [mintermFromList, BoolQuery.eval]
  | cons hd tl ih =>
      constructor
      · intro h a ha
        simp [mintermFromList, BoolQuery.eval] at h
        rcases h with ⟨hhd, htl⟩
        simp at ha
        rcases ha with rfl | htlMem
        · simpa [literalQuery_eval_iff] using hhd
        · exact (ih.mp htl) a htlMem
      · intro h
        simp [mintermFromList, BoolQuery.eval]
        constructor
        · exact (literalQuery_eval_iff S hd (assignment hd) x).mpr
            (h hd (by simp))
        · exact ih.mpr (by
            intro a ha
            exact h a (by simp [ha]))

/-- The truth-table minterm over all finite atoms. -/
noncomputable def mintermQuery {Atom : Type*} [Fintype Atom]
    (assignment : Atom -> Bool) : BoolQuery Atom :=
  mintermFromList ((Finset.univ : Finset Atom).toList) assignment

theorem mintermQuery_eval_iff_assignmentMatches {State Atom : Type*}
    [Fintype Atom]
    (S : ObligationSemantics State Atom)
    (assignment : Atom -> Bool) (x : State) :
    BoolQuery.eval S (mintermQuery assignment) x <->
      AssignmentMatches S assignment x := by
  classical
  simp [mintermQuery, AssignmentMatches, mintermFromList_eval_iff]

/-! ## Disjunction over realized assignments -/

/-- An assignment is realized by a target predicate if some target state has
exactly that atom truth table. -/
def AssignmentRealizedByTarget {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (target : State -> Prop)
    (assignment : Atom -> Bool) : Prop :=
  exists x, target x /\ AssignmentMatches S assignment x

/-- Finite disjunction over all target-realized atom assignments in a list. -/
noncomputable def disjAssignmentList {State Atom : Type*} [Fintype Atom]
    (S : ObligationSemantics State Atom) (target : State -> Prop) :
    List (Atom -> Bool) -> BoolQuery Atom
  | [] => BoolQuery.bottom
  | assignment :: rest =>
      by
        classical
        exact BoolQuery.join
          (if AssignmentRealizedByTarget S target assignment then
            mintermQuery assignment
          else
            BoolQuery.bottom)
          (disjAssignmentList S target rest)

theorem disjAssignmentList_eval_iff {State Atom : Type*}
    [Fintype Atom]
    (S : ObligationSemantics State Atom) (target : State -> Prop)
    (assignments : List (Atom -> Bool)) (x : State) :
    BoolQuery.eval S (disjAssignmentList S target assignments) x <->
      exists assignment,
        assignment ∈ assignments /\
          AssignmentRealizedByTarget S target assignment /\
          AssignmentMatches S assignment x := by
  classical
  induction assignments with
  | nil =>
      simp [disjAssignmentList, BoolQuery.eval]
  | cons hd tl ih =>
      by_cases hreal : AssignmentRealizedByTarget S target hd
      · constructor
        · intro h
          simp [disjAssignmentList, BoolQuery.eval, hreal,
            mintermQuery_eval_iff_assignmentMatches, ih] at h
          rcases h with hhd | htl
          · exact ⟨hd, by simp, hreal, hhd⟩
          · rcases htl with ⟨assignment, hmem, hrealized, hmatch⟩
            exact ⟨assignment, by simp [hmem], hrealized, hmatch⟩
        · intro h
          rcases h with ⟨assignment, hmem, hrealized, hmatch⟩
          simp at hmem
          rcases hmem with rfl | hmemTail
          · simp [disjAssignmentList, BoolQuery.eval, hreal]
            exact Or.inl
              (by simpa [mintermQuery_eval_iff_assignmentMatches] using hmatch)
          · simp [disjAssignmentList, BoolQuery.eval, hreal,
              mintermQuery_eval_iff_assignmentMatches, ih]
            exact Or.inr ⟨assignment, hmemTail, hrealized, hmatch⟩
      · constructor
        · intro h
          simp [disjAssignmentList, BoolQuery.eval, hreal, ih] at h
          rcases h with ⟨assignment, hmem, hrealized, hmatch⟩
          exact ⟨assignment, by simp [hmem], hrealized, hmatch⟩
        · intro h
          rcases h with ⟨assignment, hmem, hrealized, hmatch⟩
          simp at hmem
          rcases hmem with rfl | hmemTail
          · exact False.elim (hreal hrealized)
          · simp [disjAssignmentList, BoolQuery.eval, hreal, ih]
            exact ⟨assignment, hmemTail, hrealized, hmatch⟩

/-- The finite truth-table query generated by a target predicate. -/
noncomputable def finiteInvariantQuery {State Atom : Type*}
    [Fintype Atom] [Fintype (Atom -> Bool)]
    (S : ObligationSemantics State Atom)
    (target : State -> Prop) : BoolQuery Atom :=
  disjAssignmentList S target ((Finset.univ : Finset (Atom -> Bool)).toList)

/-! ## Finite completeness theorem -/

/-- THEOREM 1: on a finite atom vocabulary, every atom-equivalence-invariant
target predicate is expressible by a Boolean query. -/
theorem finiteInvariantQuery_eval_iff_target {State Atom : Type*}
    [Fintype Atom] [Fintype (Atom -> Bool)]
    (S : ObligationSemantics State Atom)
    (target : State -> Prop)
    (hinv :
      forall {x y}, AtomEquiv S x y -> (target x <-> target y))
    (x : State) :
    BoolQuery.eval S (finiteInvariantQuery S target) x <-> target x := by
  classical
  constructor
  · intro h
    have hdisj := (disjAssignmentList_eval_iff S target
      ((Finset.univ : Finset (Atom -> Bool)).toList) x).mp h
    rcases hdisj with ⟨assignment, _hmem, hrealized, hmatchX⟩
    rcases hrealized with ⟨y, hyTarget, hmatchY⟩
    have hyx : AtomEquiv S y x := by
      intro a
      exact (hmatchY a).trans (hmatchX a).symm
    exact (hinv hyx).mp hyTarget
  · intro hxTarget
    let assignment : Atom -> Bool :=
      fun a => if S.holds a x then true else false
    have hmatch : AssignmentMatches S assignment x := by
      intro a
      by_cases h : S.holds a x <;> simp [assignment, h]
    have hrealized : AssignmentRealizedByTarget S target assignment :=
      ⟨x, hxTarget, hmatch⟩
    have hmem :
        assignment ∈ ((Finset.univ : Finset (Atom -> Bool)).toList) := by
      simp
    exact (disjAssignmentList_eval_iff S target
      ((Finset.univ : Finset (Atom -> Bool)).toList) x).mpr
      ⟨assignment, hmem, hrealized, hmatch⟩

/-- THEOREM 2: for finite atom vocabularies, Boolean query expressibility is
equivalent to invariance under atom-equivalence. -/
theorem finite_queryExpressible_iff_atomInvariant {State Atom : Type*}
    [Fintype Atom] [Fintype (Atom -> Bool)]
    (S : ObligationSemantics State Atom) (target : State -> Prop) :
    QueryExpressible S target <->
      forall {x y}, AtomEquiv S x y -> (target x <-> target y) := by
  constructor
  · intro hexpr x y hxy
    exact queryExpressible_invariant S hexpr hxy
  · intro hinv
    exact ⟨finiteInvariantQuery S target,
      finiteInvariantQuery_eval_iff_target S target hinv⟩

/-- A finite facet vocabulary is complete for a family of safety predicates when
every predicate in the family is query-expressible. -/
def FiniteFacetCompleteFor {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (SafetyRelevant : (State -> Prop) -> Prop) : Prop :=
  forall target, SafetyRelevant target -> QueryExpressible S target

/-- THEOREM 3: for finite atom vocabularies, facet completeness for a family is
equivalent to atom-coverage invariance for that family. -/
theorem finite_facetComplete_iff_atomCoverage {State Atom : Type*}
    [Fintype Atom] [Fintype (Atom -> Bool)]
    (S : ObligationSemantics State Atom)
    (SafetyRelevant : (State -> Prop) -> Prop) :
    FiniteFacetCompleteFor S SafetyRelevant <->
      AtomCoverageCertificate S SafetyRelevant := by
  constructor
  · intro hcomplete
    exact atomCoverage_of_all_relevant_expressible S SafetyRelevant hcomplete
  · intro hcoverage target hrel
    exact (finite_queryExpressible_iff_atomInvariant S target).mpr
      (by
        intro x y hxy
        exact hcoverage.invariant target hrel hxy)

/-! ## The seven semantic atoms are finite -/

instance semanticAtomFintype : Fintype SemanticAtom where
  elems :=
    { SemanticAtom.sourceReachability,
      SemanticAtom.authorityMonotonicity,
      SemanticAtom.graphConfluence,
      SemanticAtom.gaugeInvariance,
      SemanticAtom.contractionCertification,
      SemanticAtom.omegaGluing,
      SemanticAtom.freshnessValidity }
  complete := by
    intro a
    cases a <;> simp

/-- THEOREM 4: for the seven AIppocampus semantic facets, completeness for any
declared safety-relevant family is exactly the explicit atom-coverage
certificate. -/
theorem semanticFacetComplete_iff_atomCoverage {State : Type*}
    (P : CSafePredicates State)
    (SafetyRelevant : (State -> Prop) -> Prop) :
    FiniteFacetCompleteFor (semanticObligationSemantics P) SafetyRelevant <->
      AtomCoverageCertificate (semanticObligationSemantics P) SafetyRelevant := by
  classical
  exact finite_facetComplete_iff_atomCoverage
    (semanticObligationSemantics P) SafetyRelevant

/-!
  Boundary:
  - This proves a real finite-vocabulary completeness theorem, but only for
    predicates invariant under the chosen atom equivalence.
  - It does not prove that the seven AIppocampus facets cover every conceivable
    safety-relevant predicate.  It proves the exact obligation: supply
    `AtomCoverageCertificate` for the intended family, or exhibit an
    atom-equivalent separating pair to refute completeness.
-/
