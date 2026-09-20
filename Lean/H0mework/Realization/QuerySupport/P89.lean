/-
  Proposition 89: raw support discovery relations generate raw classifiers.

  Proposition 88 lowered the bridge certificate to a raw memory-atom classifier,
  but a runtime often emits a relation/table rather than total functions:

      raw memory atom m represents primitive semantic failure atom a.

  This file proves that the relation need not be bijective at the raw layer.
  It only needs:

    * every raw memory atom has some semantic support label;
    * every semantic support label has some raw representative;
    * each declared row preserves support.

  Duplicate raw memory atoms are harmless because Proposition 88 descends
  through the support quotient.  Under semantic atom independence, label
  uniqueness for each raw memory atom is forced by support extensionality; it is
  not an extra runtime obligation.
-/

import H0mework.Realization.QuerySupport.P88

/-! ## Raw support discovery relation -/

/-- A relation/table certificate from raw memory atoms to semantic failure
atoms.

Unlike `MemorySupportDiscovery` from Proposition 66, this relation does not ask
for uniqueness on the memory side or semantic side.  The quotient bridge only
needs total coverage plus row-wise support preservation. -/
structure RawAtomicSupportDiscovery {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  represents : MemoryAtom -> SemanticAtom -> Prop
  support_iff :
    forall m a,
      represents m a ->
        forall x,
          M.produces x m <->
            BoolQuery.eval (semanticObligationSemantics P)
              (singletonFailureQuery a) x
  memory_total : forall m, exists a, represents m a
  semantic_total : forall a, exists m, represents m a

namespace RawAtomicSupportDiscovery

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

noncomputable section

/-- Choose one semantic support label for a raw memory atom. -/
def toSemantic (D : RawAtomicSupportDiscovery P M) (m : MemoryAtom) :
    SemanticAtom :=
  Classical.choose (D.memory_total m)

/-- Choose one raw representative for a semantic support label. -/
def toMemory (D : RawAtomicSupportDiscovery P M) (a : SemanticAtom) :
    MemoryAtom :=
  Classical.choose (D.semantic_total a)

/-- THEOREM 1: the chosen semantic label is represented by the raw atom. -/
theorem represents_toSemantic
    (D : RawAtomicSupportDiscovery P M) (m : MemoryAtom) :
    D.represents m (D.toSemantic m) := by
  exact Classical.choose_spec (D.memory_total m)

/-- THEOREM 2: the chosen raw representative represents the semantic label. -/
theorem represents_toMemory
    (D : RawAtomicSupportDiscovery P M) (a : SemanticAtom) :
    D.represents (D.toMemory a) a := by
  exact Classical.choose_spec (D.semantic_total a)

/-- THEOREM 3: support preservation for the chosen semantic label. -/
theorem toSemantic_support_iff
    (D : RawAtomicSupportDiscovery P M) (m : MemoryAtom) (x : State) :
    M.produces x m <->
      BoolQuery.eval (semanticObligationSemantics P)
        (singletonFailureQuery (D.toSemantic m)) x := by
  exact D.support_iff m (D.toSemantic m) (D.represents_toSemantic m) x

/-- THEOREM 4: support preservation for the chosen raw representative. -/
theorem toMemory_support_iff
    (D : RawAtomicSupportDiscovery P M) (a : SemanticAtom) (x : State) :
    M.produces x (D.toMemory a) <->
      BoolQuery.eval (semanticObligationSemantics P)
        (singletonFailureQuery a) x := by
  exact D.support_iff (D.toMemory a) a (D.represents_toMemory a) x

/-- THEOREM 5: a raw discovery relation constructs the raw classifier from
Proposition 88. -/
def toRawAtomicSupportClassifier
    (D : RawAtomicSupportDiscovery P M) :
    RawAtomicSupportClassifier P M where
  supportAtom := D.toSemantic
  support_iff := D.toSemantic_support_iff
  representative := D.toMemory
  representative_iff := D.toMemory_support_iff

/-! ## Uniqueness is forced, not assumed -/

/-- THEOREM 6: under semantic atom independence, a row-wise support-preserving
raw discovery relation cannot assign two different semantic labels to the same
raw memory atom. -/
theorem represents_unique_of_independent
    (D : RawAtomicSupportDiscovery P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    {m : MemoryAtom} {a b : SemanticAtom}
    (ha : D.represents m a) (hb : D.represents m b) :
    a = b := by
  apply semanticSupportExtensional_of_independent P hind
  intro x
  calc
    AtomFailure (semanticObligationSemantics P) x a
        <-> BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery a) x :=
      (singletonFailureQuery_eval_iff P a x).symm
    _ <-> M.produces x m := (D.support_iff m a ha x).symm
    _ <-> BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery b) x :=
      D.support_iff m b hb x
    _ <-> AtomFailure (semanticObligationSemantics P) x b :=
      singletonFailureQuery_eval_iff P b x

/-! ## Bridge consequences -/

/-- THEOREM 7: under semantic atom independence, raw discovery descends to the
P87 quotient classifier. -/
noncomputable def toQuotientAtomicSupportClassifier
    (D : RawAtomicSupportDiscovery P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientAtomicSupportClassifier P M :=
  (D.toRawAtomicSupportClassifier).toQuotientAtomicSupportClassifier hind

/-- THEOREM 8: raw discovery gives singleton-failure query coverage after
quotienting. -/
theorem toSingletonFailureQueryCoverage
    (D : RawAtomicSupportDiscovery P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    SingletonFailureQueryCoverage P M := by
  exact (D.toRawAtomicSupportClassifier).toSingletonFailureQueryCoverage hind

/-- THEOREM 9: raw discovery gives quotient support coverage. -/
theorem toQuotientSupportCoverage
    (D : RawAtomicSupportDiscovery P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientSupportCoverage P M := by
  exact (D.toRawAtomicSupportClassifier).toQuotientSupportCoverage hind

/-- THEOREM 10: raw discovery constructs the strong quotient
memory/obstruction equivalence. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (D : RawAtomicSupportDiscovery P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  (D.toRawAtomicSupportClassifier).toGeneralMemoryObstructionEquivalence hind

/-- THEOREM 11: raw discovery makes raw memory production exactly global
unsafety. -/
theorem raw_production_nonempty_iff_not_csafe
    (D : RawAtomicSupportDiscovery P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  exact (D.toRawAtomicSupportClassifier).raw_production_nonempty_iff_not_csafe
    hind x

end

end RawAtomicSupportDiscovery

/-!
  Summary:
  - A runtime can emit a raw support discovery relation/table rather than
    quotient atoms or total classifier functions.
  - The relation only needs total coverage plus row-wise support iff.
  - Semantic atom independence forces per-raw-atom label uniqueness and lets
    Lean construct the raw classifier, quotient classifier, singleton coverage,
    and strong quotient memory/obstruction equivalence.
-/
