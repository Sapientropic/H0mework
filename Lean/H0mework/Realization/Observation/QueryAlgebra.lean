/-
  Proposition 20: Boolean query algebra / calculus completeness, V0.

  This closes the first, deliberately small, query-language gap: over a fixed
  set of primitive memory predicates, the Boolean query algebra and the Boolean
  predicate calculus have the same denotation.  It is a Codd-style
  algebra/calculus equivalence for the safety-obligation fragment, not a full
  relational completeness theorem for arbitrary source joins, recursion, or
  generative field interference.

  The useful bridge is practical: `C_safe` and individual reopen witnesses are
  now ordinary Boolean queries over the lower semantic atoms.
-/

import H0mework.Realization.Observation.LabelJoin

/-! ## Boolean query algebra -/

/-- Algebraic Boolean queries over primitive atoms. -/
inductive BoolQuery (Atom : Type*) where
  | top
  | bottom
  | atom : Atom → BoolQuery Atom
  | neg : BoolQuery Atom → BoolQuery Atom
  | meet : BoolQuery Atom → BoolQuery Atom → BoolQuery Atom
  | join : BoolQuery Atom → BoolQuery Atom → BoolQuery Atom

namespace BoolQuery

/-- Denotation of a Boolean query as a state predicate. -/
def eval {State Atom : Type*} (S : ObligationSemantics State Atom) :
    BoolQuery Atom → State → Prop
  | top, _x => True
  | bottom, _x => False
  | atom a, x => S.holds a x
  | neg q, x => ¬ eval S q x
  | meet p q, x => eval S p x ∧ eval S q x
  | join p q, x => eval S p x ∨ eval S q x

end BoolQuery

/-! ## Boolean predicate calculus -/

/-- Calculus-style formulas over the same primitive atoms. -/
inductive BoolCalc (Atom : Type*) where
  | truth
  | falsity
  | pred : Atom → BoolCalc Atom
  | not : BoolCalc Atom → BoolCalc Atom
  | and : BoolCalc Atom → BoolCalc Atom → BoolCalc Atom
  | or : BoolCalc Atom → BoolCalc Atom → BoolCalc Atom

namespace BoolCalc

/-- Denotation of a Boolean calculus formula as a state predicate. -/
def eval {State Atom : Type*} (S : ObligationSemantics State Atom) :
    BoolCalc Atom → State → Prop
  | truth, _x => True
  | falsity, _x => False
  | pred a, x => S.holds a x
  | not f, x => ¬ eval S f x
  | and p q, x => eval S p x ∧ eval S q x
  | or p q, x => eval S p x ∨ eval S q x

end BoolCalc

/-! ## Syntax translations -/

/-- Compile calculus formulas to algebraic queries. -/
def calcToQuery {Atom : Type*} : BoolCalc Atom → BoolQuery Atom
  | BoolCalc.truth => BoolQuery.top
  | BoolCalc.falsity => BoolQuery.bottom
  | BoolCalc.pred a => BoolQuery.atom a
  | BoolCalc.not f => BoolQuery.neg (calcToQuery f)
  | BoolCalc.and p q => BoolQuery.meet (calcToQuery p) (calcToQuery q)
  | BoolCalc.or p q => BoolQuery.join (calcToQuery p) (calcToQuery q)

/-- Decompile algebraic queries to calculus formulas. -/
def queryToCalc {Atom : Type*} : BoolQuery Atom → BoolCalc Atom
  | BoolQuery.top => BoolCalc.truth
  | BoolQuery.bottom => BoolCalc.falsity
  | BoolQuery.atom a => BoolCalc.pred a
  | BoolQuery.neg q => BoolCalc.not (queryToCalc q)
  | BoolQuery.meet p q => BoolCalc.and (queryToCalc p) (queryToCalc q)
  | BoolQuery.join p q => BoolCalc.or (queryToCalc p) (queryToCalc q)

/-- THEOREM 1: compiling calculus to algebra preserves denotation. -/
theorem calcToQuery_sound {State Atom : Type*}
    (S : ObligationSemantics State Atom) :
    ∀ f x, BoolQuery.eval S (calcToQuery f) x ↔ BoolCalc.eval S f x := by
  intro f
  induction f with
  | truth =>
      intro x
      rfl
  | falsity =>
      intro x
      rfl
  | pred a =>
      intro x
      rfl
  | not f ih =>
      intro x
      simp [calcToQuery, BoolQuery.eval, BoolCalc.eval, ih x]
  | and p q ihp ihq =>
      intro x
      simp [calcToQuery, BoolQuery.eval, BoolCalc.eval, ihp x, ihq x]
  | or p q ihp ihq =>
      intro x
      simp [calcToQuery, BoolQuery.eval, BoolCalc.eval, ihp x, ihq x]

/-- THEOREM 2: decompiling algebra to calculus preserves denotation. -/
theorem queryToCalc_sound {State Atom : Type*}
    (S : ObligationSemantics State Atom) :
    ∀ q x, BoolCalc.eval S (queryToCalc q) x ↔ BoolQuery.eval S q x := by
  intro q
  induction q with
  | top =>
      intro x
      rfl
  | bottom =>
      intro x
      rfl
  | atom a =>
      intro x
      rfl
  | neg q ih =>
      intro x
      simp [queryToCalc, BoolQuery.eval, BoolCalc.eval, ih x]
  | meet p q ihp ihq =>
      intro x
      simp [queryToCalc, BoolQuery.eval, BoolCalc.eval, ihp x, ihq x]
  | join p q ihp ihq =>
      intro x
      simp [queryToCalc, BoolQuery.eval, BoolCalc.eval, ihp x, ihq x]

/-- THEOREM 3: every calculus formula has an equivalent algebraic query. -/
theorem calculus_expressible_by_query {State Atom : Type*}
    (S : ObligationSemantics State Atom) (f : BoolCalc Atom) :
    ∃ q, ∀ x, BoolQuery.eval S q x ↔ BoolCalc.eval S f x := by
  exact ⟨calcToQuery f, calcToQuery_sound S f⟩

/-- THEOREM 4: every algebraic query has an equivalent calculus formula. -/
theorem query_expressible_by_calculus {State Atom : Type*}
    (S : ObligationSemantics State Atom) (q : BoolQuery Atom) :
    ∃ f, ∀ x, BoolCalc.eval S f x ↔ BoolQuery.eval S q x := by
  exact ⟨queryToCalc q, queryToCalc_sound S q⟩

/-! ## AIppocampus safety/reopen queries -/

/-- Query that asks whether all seven lower semantic safety atoms hold. -/
def cSafeBoolQuery : BoolQuery SemanticAtom :=
  BoolQuery.meet (BoolQuery.atom SemanticAtom.sourceReachability)
    (BoolQuery.meet (BoolQuery.atom SemanticAtom.authorityMonotonicity)
      (BoolQuery.meet (BoolQuery.atom SemanticAtom.graphConfluence)
        (BoolQuery.meet (BoolQuery.atom SemanticAtom.gaugeInvariance)
          (BoolQuery.meet (BoolQuery.atom SemanticAtom.contractionCertification)
            (BoolQuery.meet (BoolQuery.atom SemanticAtom.omegaGluing)
              (BoolQuery.atom SemanticAtom.freshnessValidity))))))

/-- THEOREM 5: `C_safe` is expressible as a Boolean query over semantic atoms. -/
theorem cSafeBoolQuery_eval_iff_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    BoolQuery.eval (semanticObligationSemantics P) cSafeBoolQuery x ↔ CSafe P x := by
  simp [cSafeBoolQuery, BoolQuery.eval, semanticObligationSemantics,
    semanticHolds, CSafe]

/-- A query for one reopen witness: the corresponding semantic atom fails. -/
def reopenWitnessQuery (r : ReopenTaxonomy) : BoolQuery SemanticAtom :=
  BoolQuery.neg (BoolQuery.atom (reopenToSemanticAtom r))

/-- THEOREM 6: each reopen witness is expressible as a Boolean query. -/
theorem reopenWitnessQuery_eval_iff_taxonomyWitness {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy) :
    BoolQuery.eval (semanticObligationSemantics P) (reopenWitnessQuery r) x ↔
      taxonomyWitness P x r := by
  cases r <;> rfl

/-- Query for being outside `C_safe`. -/
def unsafeBoolQuery : BoolQuery SemanticAtom :=
  BoolQuery.neg cSafeBoolQuery

/-- THEOREM 7: runtime unsafety is expressible as a Boolean query. -/
theorem unsafeBoolQuery_eval_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    BoolQuery.eval (semanticObligationSemantics P) unsafeBoolQuery x ↔ ¬ CSafe P x := by
  simp [unsafeBoolQuery, BoolQuery.eval, cSafeBoolQuery_eval_iff_csafe P x]

/-!
  Summary:
  - Boolean algebraic queries and Boolean calculus formulas are mutually
    expressive over the same primitive obligation predicates.
  - `C_safe`, `¬ C_safe`, and every reopen witness are ordinary queries in
    this fragment.

  Boundary:
  - This is not a full relational algebra / relational calculus completeness
    theorem.  It does not yet cover joins over source tables, quantification
    over sections, recursion, aggregation, freshness ordering, or generative
    field-interference search.
-/
