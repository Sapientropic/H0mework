/-
  Proposition 13: deriving primitive obstruction atoms from product semantics.

  Proposition 12 made obstruction canonical relative to a fixed set of cases.
  This file moves one level lower: if safety semantics is a product/conjunction
  of primitive obligations, then the primitive obstruction atoms are forced to
  be exactly the failed coordinates of that product.

  The AIppocampus reopen taxonomy is then proved to be a presentation
  (relabeling) of those lower semantic atoms, not the source of canonicity.

  Remaining debt: proving that the concrete runtime's semantic safety contract
  really is exactly this product of obligations, rather than a coarser or finer
  contract.
-/

import H0mework.Realization.Observation.CanonicalSupport

/-! ## Generic product-of-obligations semantics -/

/-- A safety semantics indexed by primitive obligation atoms. -/
structure ObligationSemantics (State Atom : Type*) where
  holds : Atom → State → Prop

/-- A state is safe when every primitive obligation holds. -/
def SafeByAtoms {State Atom : Type*}
    (S : ObligationSemantics State Atom) (x : State) : Prop :=
  ∀ a, S.holds a x

/-- The canonical primitive failure support at a state. -/
def AtomFailure {State Atom : Type*}
    (S : ObligationSemantics State Atom) (x : State) (a : Atom) : Prop :=
  ¬ S.holds a x

/-- THEOREM 1: for any product/conjunction safety semantics, unsafety is exactly
    nonempty primitive failure support. -/
theorem atomSupport_nonempty_iff_not_safe {State Atom : Type*}
    (S : ObligationSemantics State Atom) (x : State) :
    (∃ a, AtomFailure S x a) ↔ ¬ SafeByAtoms S x := by
  constructor
  · rintro ⟨a, ha⟩ hs
    exact ha (hs a)
  · intro hnot
    classical
    by_contra hno
    apply hnot
    intro a
    by_contra ha
    exact hno ⟨a, ha⟩

/-- Independence of primitive atoms: every truth assignment to obligations can
    be realized by some state. This is a semantic assumption, not automatic. -/
structure AtomIndependent {State Atom : Type*}
    (S : ObligationSemantics State Atom) where
  realize : ∀ assignment : Atom → Prop, ∃ x, ∀ a, S.holds a x ↔ assignment a

/-- THEOREM 2: under independence, no primitive atom is redundant: one can vary
    that atom while keeping all other atoms fixed. -/
theorem atom_irreducible_of_independent {State Atom : Type*}
    [DecidableEq Atom]
    (S : ObligationSemantics State Atom)
    (hind : AtomIndependent S) (a : Atom) :
    ∃ x y,
      S.holds a x ∧ ¬ S.holds a y ∧
      ∀ b, b ≠ a → (S.holds b x ↔ S.holds b y) := by
  classical
  let allTrue : Atom → Prop := fun _ => True
  let exceptA : Atom → Prop := fun b => b ≠ a
  rcases hind.realize allTrue with ⟨x, hx⟩
  rcases hind.realize exceptA with ⟨y, hy⟩
  refine ⟨x, y, ?_, ?_, ?_⟩
  · exact (hx a).mpr trivial
  · intro hy_a
    exact (hy a).mp hy_a rfl
  · intro b hb
    constructor
    · intro _hxb
      exact (hy b).mpr hb
    · intro _hyb
      exact (hx b).mpr trivial

/-- The free product semantics over atoms: a state is just an assignment of
    truth values to atoms. -/
def freeObligationSemantics (Atom : Type*) :
    ObligationSemantics (Atom → Prop) Atom where
  holds := fun a assignment => assignment a

/-- THEOREM 3: the free product semantics realizes every assignment. -/
theorem freeObligationSemantics_independent (Atom : Type*) :
    AtomIndependent (freeObligationSemantics Atom) where
  realize := by
    intro assignment
    exact ⟨assignment, by intro _a; rfl⟩

/-! ## AIppocampus lower semantic atoms -/

/-- Lower semantic atoms. These are not reopen labels; they are the coordinates
    of the safety contract. -/
inductive SemanticAtom where
  | sourceReachability
  | authorityMonotonicity
  | graphConfluence
  | gaugeInvariance
  | contractionCertification
  | omegaGluing
  | freshnessValidity
  deriving DecidableEq, Repr

/-- The lower semantic obligation associated with each atom. -/
def semanticHolds {State : Type*}
    (P : CSafePredicates State) : SemanticAtom → State → Prop
  | SemanticAtom.sourceReachability => P.sourceBacked
  | SemanticAtom.authorityMonotonicity => P.authoritySafe
  | SemanticAtom.graphConfluence => P.graphConfluent
  | SemanticAtom.gaugeInvariance => P.gaugeNonleaking
  | SemanticAtom.contractionCertification => P.contractionSafe
  | SemanticAtom.omegaGluing => P.omegaConsistent
  | SemanticAtom.freshnessValidity => P.freshnessSafe

/-- AIppocampus safety as product-of-obligations semantics. -/
def semanticObligationSemantics {State : Type*}
    (P : CSafePredicates State) : ObligationSemantics State SemanticAtom where
  holds := semanticHolds P

/-- THEOREM 4: safety by lower semantic atoms is exactly `C_safe`. -/
theorem semanticSafe_iff_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    SafeByAtoms (semanticObligationSemantics P) x ↔ CSafe P x := by
  constructor
  · intro h
    exact ⟨
      h SemanticAtom.sourceReachability,
      h SemanticAtom.authorityMonotonicity,
      h SemanticAtom.graphConfluence,
      h SemanticAtom.gaugeInvariance,
      h SemanticAtom.contractionCertification,
      h SemanticAtom.omegaGluing,
      h SemanticAtom.freshnessValidity
    ⟩
  · intro hx a
    cases a with
    | sourceReachability => exact hx.1
    | authorityMonotonicity => exact hx.2.1
    | graphConfluence => exact hx.2.2.1
    | gaugeInvariance => exact hx.2.2.2.1
    | contractionCertification => exact hx.2.2.2.2.1
    | omegaGluing => exact hx.2.2.2.2.2.1
    | freshnessValidity => exact hx.2.2.2.2.2.2

/-- THEOREM 5: unsafety is exactly nonempty lower semantic failure support. -/
theorem semanticFailure_nonempty_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    (∃ a, AtomFailure (semanticObligationSemantics P) x a) ↔ ¬ CSafe P x := by
  constructor
  · intro hfail hsafe
    have hnotSafe : ¬ SafeByAtoms (semanticObligationSemantics P) x :=
      (atomSupport_nonempty_iff_not_safe (semanticObligationSemantics P) x).mp hfail
    exact hnotSafe ((semanticSafe_iff_csafe P x).mpr hsafe)
  · intro hnot
    exact (atomSupport_nonempty_iff_not_safe (semanticObligationSemantics P) x).mpr
      (fun hsafe => hnot ((semanticSafe_iff_csafe P x).mp hsafe))

/-! ## Reopen taxonomy as a presentation of lower semantic atoms -/

/-- Relabel lower semantic atoms as reopen taxonomy cases. -/
def semanticAtomToReopen : SemanticAtom → ReopenTaxonomy
  | SemanticAtom.sourceReachability => ReopenTaxonomy.sourceMissing
  | SemanticAtom.authorityMonotonicity => ReopenTaxonomy.authorityOverreach
  | SemanticAtom.graphConfluence => ReopenTaxonomy.graphNonconfluent
  | SemanticAtom.gaugeInvariance => ReopenTaxonomy.gaugeLeak
  | SemanticAtom.contractionCertification => ReopenTaxonomy.contractionUncertified
  | SemanticAtom.omegaGluing => ReopenTaxonomy.omegaConflict
  | SemanticAtom.freshnessValidity => ReopenTaxonomy.freshnessStale

/-- Decode reopen taxonomy cases back to lower semantic atoms. -/
def reopenToSemanticAtom : ReopenTaxonomy → SemanticAtom
  | ReopenTaxonomy.sourceMissing => SemanticAtom.sourceReachability
  | ReopenTaxonomy.authorityOverreach => SemanticAtom.authorityMonotonicity
  | ReopenTaxonomy.graphNonconfluent => SemanticAtom.graphConfluence
  | ReopenTaxonomy.gaugeLeak => SemanticAtom.gaugeInvariance
  | ReopenTaxonomy.contractionUncertified => SemanticAtom.contractionCertification
  | ReopenTaxonomy.omegaConflict => SemanticAtom.omegaGluing
  | ReopenTaxonomy.freshnessStale => SemanticAtom.freshnessValidity

/-- THEOREM 6: taxonomy encoding then decoding is identity on semantic atoms. -/
theorem reopen_semantic_left_inverse :
    ∀ a, reopenToSemanticAtom (semanticAtomToReopen a) = a := by
  intro a
  cases a <;> rfl

/-- THEOREM 7: decoding then encoding is identity on taxonomy cases. -/
theorem reopen_semantic_right_inverse :
    ∀ r, semanticAtomToReopen (reopenToSemanticAtom r) = r := by
  intro r
  cases r <;> rfl

/-- THEOREM 8: taxonomy witnesses are exactly lower semantic atom failures. -/
theorem taxonomyWitness_iff_semanticFailure {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy) :
    taxonomyWitness P x r ↔
      AtomFailure (semanticObligationSemantics P) x (reopenToSemanticAtom r) := by
  cases r <;> rfl

/-- THEOREM 9: lower semantic atom failures are exactly taxonomy witnesses under
    the taxonomy presentation. -/
theorem semanticFailure_iff_taxonomyWitness {State : Type*}
    (P : CSafePredicates State) (x : State) (a : SemanticAtom) :
    AtomFailure (semanticObligationSemantics P) x a ↔
      taxonomyWitness P x (semanticAtomToReopen a) := by
  cases a <;> rfl

/-!
  Summary:
  - In a product/conjunction safety semantics, primitive obstruction atoms are
    the failed coordinates of the product.
  - Under independence, each coordinate is irreducible.
  - The AIppocampus reopen taxonomy is an isomorphic presentation of lower
    semantic atoms, not the source of canonicity.

  Remaining debt: prove that the concrete runtime safety contract really has
  this product-of-obligations shape and that the listed lower atoms are the
  complete primitive coordinates of that contract.
-/
