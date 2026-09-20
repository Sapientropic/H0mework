/-
  Proposition 14: primitive atoms as minimal semantic failure supports.

  Proposition 13 showed that a product-of-obligations safety semantics has a
  canonical support object: the failed coordinates of the product.  This file
  pushes one step lower.  A primitive atom is not a chosen reopen label; it is a
  coordinate that can appear as a singleton/minimal failure support.

  Under the independence hypothesis from Proposition 13, every obligation
  coordinate is forced in this sense.  The reopen taxonomy is then only a
  lossless presentation of these singleton semantic failures.

  Remaining debt: proving that the concrete runtime safety contract satisfies
  the required independence / exact-product assumptions.
-/

import H0mework.Realization.Observation.ObligationProduct

/-! ## Minimal failure supports -/

/-- A state has exactly one failed primitive atom. -/
def SingletonFailure {State Atom : Type*}
    (S : ObligationSemantics State Atom) (x : State) (a : Atom) : Prop :=
  AtomFailure S x a ∧ ∀ b, AtomFailure S x b → b = a

/-- A primitive failure atom is one that can appear as a singleton obstruction. -/
def PrimitiveFailureAtom {State Atom : Type*}
    (S : ObligationSemantics State Atom) (a : Atom) : Prop :=
  ∃ x, SingletonFailure S x a

/-- THEOREM 1: a singleton failure is unsafe. -/
theorem singletonFailure_not_safe {State Atom : Type*}
    (S : ObligationSemantics State Atom) {x : State} {a : Atom}
    (h : SingletonFailure S x a) :
    ¬ SafeByAtoms S x := by
  exact (atomSupport_nonempty_iff_not_safe S x).mp ⟨a, h.1⟩

/-- THEOREM 2: in an independent product semantics, every atom can be realized
    as the sole failed coordinate. -/
theorem singletonFailure_of_independent {State Atom : Type*}
    [DecidableEq Atom]
    (S : ObligationSemantics State Atom)
    (hind : AtomIndependent S) (a : Atom) :
    ∃ x, SingletonFailure S x a := by
  classical
  let assignment : Atom → Prop := fun b => b ≠ a
  rcases hind.realize assignment with ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · intro hholds
    exact (hx a).mp hholds rfl
  · intro b hb
    by_contra hne
    exact hb ((hx b).mpr hne)

/-- THEOREM 3: under independence, every atom is primitive. -/
theorem primitiveAtom_of_independent {State Atom : Type*}
    [DecidableEq Atom]
    (S : ObligationSemantics State Atom)
    (hind : AtomIndependent S) :
    ∀ a, PrimitiveFailureAtom S a := by
  intro a
  exact singletonFailure_of_independent S hind a

/-- THEOREM 4: the free product semantics forces every atom as a primitive
    failure atom. -/
theorem freePrimitiveAtoms (Atom : Type*) [DecidableEq Atom] :
    ∀ a, PrimitiveFailureAtom (freeObligationSemantics Atom) a := by
  exact primitiveAtom_of_independent
    (freeObligationSemantics Atom)
    (freeObligationSemantics_independent Atom)

/-! ## Transporting singleton supports through the reopen presentation -/

/-- Semantic singleton failures are just singleton failures for the
    AIppocampus lower-obligation semantics. -/
def SemanticSingletonFailure {State : Type*}
    (P : CSafePredicates State) (x : State) (a : SemanticAtom) : Prop :=
  SingletonFailure (semanticObligationSemantics P) x a

/-- A reopen taxonomy case is the unique failed case at a state. -/
def ReopenSingletonFailure {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy) : Prop :=
  taxonomyWitness P x r ∧ ∀ r', taxonomyWitness P x r' → r' = r

/-- THEOREM 5: singleton semantic failures transport across the taxonomy
    isomorphism. -/
theorem semanticSingleton_iff_reopenSingleton {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy) :
    SemanticSingletonFailure P x (reopenToSemanticAtom r) ↔
      ReopenSingletonFailure P x r := by
  constructor
  · intro h
    constructor
    · exact (taxonomyWitness_iff_semanticFailure P x r).mpr h.1
    · intro r' hr'
      have hs : AtomFailure (semanticObligationSemantics P) x
          (reopenToSemanticAtom r') :=
        (taxonomyWitness_iff_semanticFailure P x r').mp hr'
      have hatom : reopenToSemanticAtom r' = reopenToSemanticAtom r := h.2 _ hs
      calc
        r' = semanticAtomToReopen (reopenToSemanticAtom r') := by
          exact (reopen_semantic_right_inverse r').symm
        _ = semanticAtomToReopen (reopenToSemanticAtom r) := by
          rw [hatom]
        _ = r := reopen_semantic_right_inverse r
  · intro h
    constructor
    · exact (taxonomyWitness_iff_semanticFailure P x r).mp h.1
    · intro a ha
      let r' := semanticAtomToReopen a
      have hr' : taxonomyWitness P x r' :=
        (semanticFailure_iff_taxonomyWitness P x a).mp ha
      have htax : r' = r := h.2 r' hr'
      calc
        a = reopenToSemanticAtom (semanticAtomToReopen a) := by
          exact (reopen_semantic_left_inverse a).symm
        _ = reopenToSemanticAtom r := by
          have hdecode : reopenToSemanticAtom r' = reopenToSemanticAtom r :=
            congrArg reopenToSemanticAtom htax
          simpa [r'] using hdecode

/-- THEOREM 6: if the lower semantic obligations are independent, every reopen
    taxonomy case is forced as a singleton/minimal obstruction. -/
theorem reopenSingleton_of_semantic_independent {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (r : ReopenTaxonomy) :
    ∃ x, ReopenSingletonFailure P x r := by
  classical
  rcases singletonFailure_of_independent
    (semanticObligationSemantics P) hind (reopenToSemanticAtom r) with ⟨x, hx⟩
  exact ⟨x, (semanticSingleton_iff_reopenSingleton P x r).mp hx⟩

/-- THEOREM 7: if a state has a singleton semantic failure, the corresponding
    reopen case is uniquely forced. -/
theorem reopenSingleton_of_semanticSingleton {State : Type*}
    (P : CSafePredicates State) (x : State) (a : SemanticAtom)
    (h : SemanticSingletonFailure P x a) :
    ReopenSingletonFailure P x (semanticAtomToReopen a) := by
  have hcast : SemanticSingletonFailure P x
      (reopenToSemanticAtom (semanticAtomToReopen a)) := by
    simpa [reopen_semantic_left_inverse a] using h
  exact (semanticSingleton_iff_reopenSingleton P x (semanticAtomToReopen a)).mp hcast

/-- THEOREM 8: if a state has a singleton reopen failure, the corresponding
    lower semantic atom is primitive. -/
theorem primitiveSemanticAtom_of_reopenSingleton {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy)
    (h : ReopenSingletonFailure P x r) :
    PrimitiveFailureAtom (semanticObligationSemantics P) (reopenToSemanticAtom r) := by
  exact ⟨x, (semanticSingleton_iff_reopenSingleton P x r).mpr h⟩

/-!
  Summary:
  - Primitive obstruction atoms are the singleton/minimal failure supports of a
    product-of-obligations safety semantics.
  - Independence forces every obligation coordinate to be primitive; no
    coordinate is merely decorative.
  - The reopen taxonomy inherits canonicity only by transporting these
    singleton semantic failures through the Proposition 13 isomorphism.
-/
