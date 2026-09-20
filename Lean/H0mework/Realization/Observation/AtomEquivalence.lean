/-
  Proposition 23: no-free-completeness boundary for generated queries.

  Proposition 20 proves a Boolean algebra/calculus equivalence over a fixed
  primitive predicate vocabulary.  This file proves the converse boundary that
  matters for "full paradigm" claims:

    any query generated from a primitive vocabulary is invariant under the
    equivalence relation induced by that vocabulary.

  Therefore facet/query completeness cannot be proved from the algebra alone.
  It needs a semantic coverage certificate: every safety-relevant distinction
  must already be visible to the chosen primitive atoms.  If two states agree
  on every primitive atom but a proposed safety predicate separates them, that
  predicate is not expressible by the generated query language.
-/

import H0mework.Realization.Observation.PhaseVisibility

/-! ## Atom-induced observational equivalence -/

/-- Two states are equivalent for a primitive predicate vocabulary when every
    atom has the same truth value on both states. -/
def AtomEquiv {State Atom : Type*}
    (S : ObligationSemantics State Atom) (x y : State) : Prop :=
  ∀ a, S.holds a x ↔ S.holds a y

theorem atomEquiv_refl {State Atom : Type*}
    (S : ObligationSemantics State Atom) (x : State) :
    AtomEquiv S x x := by
  intro _a
  rfl

theorem atomEquiv_symm {State Atom : Type*}
    {S : ObligationSemantics State Atom} {x y : State}
    (h : AtomEquiv S x y) :
    AtomEquiv S y x := by
  intro a
  exact (h a).symm

theorem atomEquiv_trans {State Atom : Type*}
    {S : ObligationSemantics State Atom} {x y z : State}
    (hxy : AtomEquiv S x y) (hyz : AtomEquiv S y z) :
    AtomEquiv S x z := by
  intro a
  exact Iff.trans (hxy a) (hyz a)

/-! ## Generated queries cannot see past atom equivalence -/

/-- THEOREM 1: Boolean algebraic queries are invariant under atom equivalence. -/
theorem boolQuery_invariant_of_atomEquiv {State Atom : Type*}
    (S : ObligationSemantics State Atom) {x y : State}
    (hxy : AtomEquiv S x y) :
    ∀ q, BoolQuery.eval S q x ↔ BoolQuery.eval S q y := by
  intro q
  induction q with
  | top =>
      rfl
  | bottom =>
      rfl
  | atom a =>
      exact hxy a
  | neg q ih =>
      simp [BoolQuery.eval, ih]
  | meet p q ihp ihq =>
      simp [BoolQuery.eval, ihp, ihq]
  | join p q ihp ihq =>
      simp [BoolQuery.eval, ihp, ihq]

/-- THEOREM 2: Boolean calculus formulas are invariant under atom equivalence. -/
theorem boolCalc_invariant_of_atomEquiv {State Atom : Type*}
    (S : ObligationSemantics State Atom) {x y : State}
    (hxy : AtomEquiv S x y) :
    ∀ f, BoolCalc.eval S f x ↔ BoolCalc.eval S f y := by
  intro f
  induction f with
  | truth =>
      rfl
  | falsity =>
      rfl
  | pred a =>
      exact hxy a
  | not f ih =>
      simp [BoolCalc.eval, ih]
  | and p q ihp ihq =>
      simp [BoolCalc.eval, ihp, ihq]
  | or p q ihp ihq =>
      simp [BoolCalc.eval, ihp, ihq]

/-- A state predicate is expressible by the generated Boolean query algebra. -/
def QueryExpressible {State Atom : Type*}
    (S : ObligationSemantics State Atom) (target : State → Prop) : Prop :=
  ∃ q, ∀ x, BoolQuery.eval S q x ↔ target x

/-- THEOREM 3: every generated-query predicate is atom-equivalence invariant. -/
theorem queryExpressible_invariant {State Atom : Type*}
    (S : ObligationSemantics State Atom) {target : State → Prop}
    (hexpr : QueryExpressible S target) :
    ∀ {x y}, AtomEquiv S x y → (target x ↔ target y) := by
  rcases hexpr with ⟨q, hq⟩
  intro x y hxy
  calc
    target x ↔ BoolQuery.eval S q x := (hq x).symm
    _ ↔ BoolQuery.eval S q y := boolQuery_invariant_of_atomEquiv S hxy q
    _ ↔ target y := hq y

/-- THEOREM 4: if a target separates atom-equivalent states, it is not
    expressible by the generated query language. -/
theorem not_queryExpressible_of_atomEquiv_separates {State Atom : Type*}
    (S : ObligationSemantics State Atom) {target : State → Prop}
    {x y : State} (hxy : AtomEquiv S x y)
    (hsep : target x ∧ ¬ target y) :
    ¬ QueryExpressible S target := by
  intro hexpr
  have hinv := queryExpressible_invariant S hexpr hxy
  exact hsep.2 (hinv.mp hsep.1)

/-! ## Safety-facet completeness as an explicit certificate -/

/-- A family of safety-relevant predicates is covered by the primitive atoms
    when every predicate in that family is invariant under atom equivalence. -/
structure AtomCoverageCertificate {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (SafetyRelevant : (State → Prop) → Prop) where
  invariant :
    ∀ target, SafetyRelevant target →
      ∀ {x y}, AtomEquiv S x y → (target x ↔ target y)

/-- THEOREM 5: expressibility of every safety-relevant predicate implies an
    atom-coverage certificate. -/
theorem atomCoverage_of_all_relevant_expressible {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    (SafetyRelevant : (State → Prop) → Prop)
    (hexpr : ∀ target, SafetyRelevant target → QueryExpressible S target) :
    AtomCoverageCertificate S SafetyRelevant where
  invariant := by
    intro target hrel x y hxy
    exact queryExpressible_invariant S (hexpr target hrel) hxy

/-- THEOREM 6: a single safety-relevant predicate that separates
    atom-equivalent states refutes any "all relevant predicates are
    expressible" completeness claim. -/
theorem not_all_relevant_expressible_of_atomEquiv_counterexample
    {State Atom : Type*}
    (S : ObligationSemantics State Atom)
    {SafetyRelevant : (State → Prop) → Prop}
    {target : State → Prop} (hrel : SafetyRelevant target)
    {x y : State} (hxy : AtomEquiv S x y)
    (hsep : target x ∧ ¬ target y) :
    ¬ (∀ target, SafetyRelevant target → QueryExpressible S target) := by
  intro hall
  exact not_queryExpressible_of_atomEquiv_separates S hxy hsep (hall target hrel)

/-- THEOREM 7: `C_safe` itself is invariant under the seven lower semantic
    atoms.  This explains why Proposition 20 can express it as a query. -/
theorem cSafe_invariant_of_semanticAtomEquiv {State : Type*}
    (P : CSafePredicates State) {x y : State}
    (hxy : AtomEquiv (semanticObligationSemantics P) x y) :
    CSafe P x ↔ CSafe P y := by
  have hquery := boolQuery_invariant_of_atomEquiv
    (semanticObligationSemantics P) hxy cSafeBoolQuery
  calc
    CSafe P x ↔ BoolQuery.eval (semanticObligationSemantics P) cSafeBoolQuery x :=
      (cSafeBoolQuery_eval_iff_csafe P x).symm
    _ ↔ BoolQuery.eval (semanticObligationSemantics P) cSafeBoolQuery y := hquery
    _ ↔ CSafe P y := cSafeBoolQuery_eval_iff_csafe P y

/-!
  Summary:
  - Generated Boolean queries are exactly blind to distinctions outside their
    primitive atom vocabulary.
  - A real completeness theorem for the seven AIppocampus facets therefore
    needs an explicit coverage certificate saying every safety-relevant
    predicate is invariant under `semanticObligationSemantics` atom equivalence.
  - Without that certificate, a counterexample pair of atom-equivalent states
    that differs on a safety-relevant predicate formally refutes full
    expressibility.
-/
