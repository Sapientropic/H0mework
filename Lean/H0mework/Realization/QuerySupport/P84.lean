/-
  Proposition 84: support coverage is the exact remaining bridge obligation.

  Proposition 82 made memory/obstruction discovery canonical as support
  equality.  Proposition 83 quotiented memory atoms by support, so memory-side
  support extensionality is automatic.

  This file pins down what is left.  After quotienting memory atoms, the
  remaining bridge condition is exactly support coverage:

    * every quotient memory support is a semantic obstruction support;
    * every semantic obstruction support is represented by a quotient memory
      support.

  This condition is necessary for any generalized memory/obstruction
  equivalence.  Under semantic atom independence, it is also sufficient, via
  the canonical support-equality discovery theorem from Proposition 82.

  Boundary: this still does not prove seven-facet completeness.  It proves that
  the unproved part has a precise mathematical shape: support coverage.
-/

import H0mework.Realization.QuerySupport.P83

/-! ## Quotient support coverage -/

/-- Coverage of semantic obstruction supports by quotient memory supports, and
vice versa. -/
def QuotientSupportCoverage {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) : Prop :=
  (forall q : MemorySupportQuotient M,
      exists a : SemanticAtom,
        MemorySemanticSupportEq P (memorySupportQuotientContract M) q a) /\
    (forall a : SemanticAtom,
      exists q : MemorySupportQuotient M,
        MemorySemanticSupportEq P (memorySupportQuotientContract M) q a)

/-- The memory-to-semantic half of quotient support coverage. -/
def QuotientMemorySupportCovered {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) : Prop :=
  forall q : MemorySupportQuotient M,
    exists a : SemanticAtom,
      MemorySemanticSupportEq P (memorySupportQuotientContract M) q a

/-- The semantic-to-memory half of quotient support coverage. -/
def SemanticSupportCoveredByQuotientMemory {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) : Prop :=
  forall a : SemanticAtom,
    exists q : MemorySupportQuotient M,
      MemorySemanticSupportEq P (memorySupportQuotientContract M) q a

/-! ## Necessity: any equivalence implies support coverage -/

/-- THEOREM 1: any generalized memory/obstruction equivalence on the support
quotient necessarily yields quotient support coverage. -/
theorem quotientSupportCoverage_of_generalEquivalence
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (E :
      GeneralMemoryObstructionEquivalence P
        (memorySupportQuotientContract M)) :
    QuotientSupportCoverage P M := by
  constructor
  · intro q
    exact ⟨E.atomEquiv q, by
      intro x
      exact E.produces_iff_obstruction x q⟩
  · intro a
    refine ⟨E.atomEquiv.symm a, ?_⟩
    intro x
    have h :
        (memorySupportQuotientContract M).produces x
            (E.atomEquiv.symm a) <->
          AtomFailure (semanticObligationSemantics P) x
            (E.atomEquiv (E.atomEquiv.symm a)) :=
      E.produces_iff_obstruction x (E.atomEquiv.symm a)
    simpa using h

/-! ## Sufficiency: coverage plus semantic independence constructs equivalence -/

/-- THEOREM 2: under semantic atom independence, quotient support coverage
constructs the generalized memory/obstruction equivalence. -/
noncomputable def generalEquivalence_of_quotientSupportCoverage
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (hcov : QuotientSupportCoverage P M) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  (supportEqualityDiscovery_of_quotient_and_semantic_independent
    P M hind hcov.1 hcov.2).toGeneralMemoryObstructionEquivalence

/-- THEOREM 3: after quotienting, support coverage is equivalent to the
existence of a generalized memory/obstruction equivalence, provided semantic
atoms are independent. -/
theorem quotientSupportCoverage_iff_nonempty_generalEquivalence
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientSupportCoverage P M <->
      Nonempty
        (GeneralMemoryObstructionEquivalence P
          (memorySupportQuotientContract M)) := by
  constructor
  · intro hcov
    exact ⟨generalEquivalence_of_quotientSupportCoverage P M hind hcov⟩
  · rintro ⟨E⟩
    exact quotientSupportCoverage_of_generalEquivalence P M E

/-- THEOREM 4: in the covered quotient case, nonempty quotient memory
production is exactly global unsafety. -/
theorem quotientCoverage_production_nonempty_iff_not_csafe
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (hcov : QuotientSupportCoverage P M)
    (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      (CSafe P x -> False) :=
  quotient_production_nonempty_iff_not_csafe P M hind hcov.1 hcov.2 x

/-- THEOREM 5: the covered quotient equivalence gives the greatest silent
domain property for quotient memory production. -/
theorem quotientCoverage_cSafe_greatest_memory_silent_domain
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (hcov : QuotientSupportCoverage P M) :
    IsGreatestMemoryContractSilentDomain
      (memorySupportQuotientContract M) (CSafe P) :=
  (supportEqualityDiscovery_of_quotient_and_semantic_independent
    P M hind hcov.1 hcov.2).cSafe_greatest_memory_silent_domain

/-!
  Summary:
  - General memory/obstruction equivalence on quotient memory atoms always
    implies support coverage.
  - Semantic independence plus support coverage constructs that equivalence.
  - Therefore, after quotienting duplicate memory atoms, support coverage is
    the exact remaining bridge obligation.
-/
