/-
  Proposition 87: runtime-facing atomic support classifier.

  Proposition 85 rewrote quotient support coverage as singleton-failure query
  coverage.  That is the right mathematical obligation, but it is still a
  predicate.  This file packages the same obligation as the certificate shape a
  runtime or ontology store can actually emit:

    * classify each quotient memory support by the primitive semantic failure
      query that generates it;
    * provide, for each primitive semantic failure query, a quotient memory
      support that represents it.

  Lean proves that this classifier certificate is equivalent to P85 coverage,
  and therefore equivalent to the P84 bridge obligation under semantic atom
  independence.
-/

import H0mework.Realization.QuerySupport.P85

/-! ## Runtime-facing classifier certificate -/

/-- A concrete classifier/representative certificate for quotient memory
supports.

`supportAtom q` answers "which primitive failure support is this quotient memory
atom?", while `representative a` answers "which quotient memory atom represents
this primitive failure?"  The two iff fields are the actual support checks; the
names alone carry no authority. -/
structure QuotientAtomicSupportClassifier {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  supportAtom : MemorySupportQuotient M -> SemanticAtom
  support_iff :
    forall q x,
      (memorySupportQuotientContract M).produces x q <->
        BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery (supportAtom q)) x
  representative : SemanticAtom -> MemorySupportQuotient M
  representative_iff :
    forall a x,
      (memorySupportQuotientContract M).produces x (representative a) <->
        BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery a) x

namespace QuotientAtomicSupportClassifier

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 1: a classifier yields the memory-to-semantic half of singleton
failure query coverage. -/
theorem memory_generated
    (C : QuotientAtomicSupportClassifier P M) :
    QuotientMemorySupportGeneratedBySingletonFailure P M := by
  intro q
  exact ⟨C.supportAtom q, C.support_iff q⟩

/-- THEOREM 2: a classifier yields the semantic-to-memory half of singleton
failure query coverage. -/
theorem semantic_represented
    (C : QuotientAtomicSupportClassifier P M) :
    SingletonFailureGeneratedByQuotientMemorySupport P M := by
  intro a
  exact ⟨C.representative a, C.representative_iff a⟩

/-- THEOREM 3: a classifier is exactly a concrete witness of P85 singleton
failure query coverage. -/
theorem toSingletonFailureQueryCoverage
    (C : QuotientAtomicSupportClassifier P M) :
    SingletonFailureQueryCoverage P M := by
  exact ⟨C.memory_generated, C.semantic_represented⟩

/-- THEOREM 4: a classifier gives P84 quotient support coverage. -/
theorem toQuotientSupportCoverage
    (C : QuotientAtomicSupportClassifier P M) :
    QuotientSupportCoverage P M := by
  exact (quotientSupportCoverage_iff_singletonFailureQueryCoverage P M).mpr
    C.toSingletonFailureQueryCoverage

/-- THEOREM 5: under semantic atom independence, a classifier constructs the
strong quotient memory/obstruction equivalence from P84. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (C : QuotientAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  generalEquivalence_of_quotientSupportCoverage P M hind
    C.toQuotientSupportCoverage

/-- THEOREM 6: under semantic atom independence, a classifier makes quotient
memory production exactly global unsafety. -/
theorem production_nonempty_iff_not_csafe
    (C : QuotientAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      (CSafe P x -> False) := by
  exact quotientCoverage_production_nonempty_iff_not_csafe
    P M hind C.toQuotientSupportCoverage x

end QuotientAtomicSupportClassifier

/-! ## Equivalence with P85 coverage -/

noncomputable section

/-- THEOREM 7: P85 singleton coverage noncomputably constructs a classifier.

This is useful for the abstract theorem, but runtime code should provide the
classifier directly rather than rely on choice. -/
def classifier_of_singletonFailureQueryCoverage {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hcov : SingletonFailureQueryCoverage P M) :
    QuotientAtomicSupportClassifier P M where
  supportAtom := fun q => Classical.choose (hcov.1 q)
  support_iff := by
    intro q
    exact Classical.choose_spec (hcov.1 q)
  representative := fun a => Classical.choose (hcov.2 a)
  representative_iff := by
    intro a
    exact Classical.choose_spec (hcov.2 a)

/-- THEOREM 8: singleton-failure query coverage is equivalent to nonempty
classifier certificates. -/
theorem singletonFailureQueryCoverage_iff_nonempty_classifier
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) :
    SingletonFailureQueryCoverage P M <->
      Nonempty (QuotientAtomicSupportClassifier P M) := by
  constructor
  · intro hcov
    exact ⟨classifier_of_singletonFailureQueryCoverage P M hcov⟩
  · rintro ⟨C⟩
    exact C.toSingletonFailureQueryCoverage

/-- THEOREM 9: quotient support coverage is equivalent to nonempty classifier
certificates. -/
theorem quotientSupportCoverage_iff_nonempty_classifier
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) :
    QuotientSupportCoverage P M <->
      Nonempty (QuotientAtomicSupportClassifier P M) := by
  calc
    QuotientSupportCoverage P M <->
        SingletonFailureQueryCoverage P M :=
      quotientSupportCoverage_iff_singletonFailureQueryCoverage P M
    _ <-> Nonempty (QuotientAtomicSupportClassifier P M) :=
      singletonFailureQueryCoverage_iff_nonempty_classifier P M

/-- THEOREM 10: under semantic atom independence, the existence of a strong
quotient memory/obstruction equivalence is equivalent to the existence of a
runtime-facing atomic support classifier. -/
theorem generalEquivalence_iff_nonempty_classifier
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    Nonempty
        (GeneralMemoryObstructionEquivalence P
          (memorySupportQuotientContract M)) <->
      Nonempty (QuotientAtomicSupportClassifier P M) := by
  calc
    Nonempty
        (GeneralMemoryObstructionEquivalence P
          (memorySupportQuotientContract M)) <->
        QuotientSupportCoverage P M :=
      (quotientSupportCoverage_iff_nonempty_generalEquivalence P M hind).symm
    _ <-> Nonempty (QuotientAtomicSupportClassifier P M) :=
      quotientSupportCoverage_iff_nonempty_classifier P M

end

/-!
  Summary:
  - `QuotientAtomicSupportClassifier` is the runtime-facing version of the P84
    / P85 bridge obligation.
  - Abstract coverage can construct such a classifier by choice, but runtime
    mechanism-faithfulness should emit the classifier explicitly.
  - With semantic atom independence, "there exists a strong quotient
    memory/obstruction equivalence" is equivalent to "there exists an atomic
    support classifier."
-/
