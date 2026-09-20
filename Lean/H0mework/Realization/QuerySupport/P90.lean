/-
  Proposition 90: finite raw support discovery tables.

  Proposition 89 reduced the remaining runtime certificate to a raw support
  discovery relation.  This file lowers the interface one more practical step:
  a runtime can emit a finite table of rows

      (raw memory atom, primitive semantic failure atom).

  If every row has a support-iff proof and the table covers both sides, Lean
  constructs the P89 relation/table certificate and therefore all downstream
  bridge consequences.  This is the closest Lean-side shape to a JSON/SQLite
  runtime certificate.
-/

import H0mework.Realization.QuerySupport.P89

/-! ## Finite table certificate -/

/-- A finite raw support-discovery table.

Rows are intentionally allowed to contain duplicate raw atoms or duplicate
semantic atoms.  Duplicates are harmless: support quotienting removes duplicate
memory supports, and semantic atom independence forces any two support-preserving
labels for the same raw memory atom to be equal. -/
structure RawAtomicSupportDiscoveryTable {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  rows : List (MemoryAtom × SemanticAtom)
  row_support_iff :
    forall m a,
      (m, a) ∈ rows ->
        forall x,
          M.produces x m <->
            BoolQuery.eval (semanticObligationSemantics P)
              (singletonFailureQuery a) x
  memory_total : forall m, exists a, (m, a) ∈ rows
  semantic_total : forall a, exists m, (m, a) ∈ rows

namespace RawAtomicSupportDiscoveryTable

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- The relation represented by the finite table. -/
def represents (T : RawAtomicSupportDiscoveryTable P M)
    (m : MemoryAtom) (a : SemanticAtom) : Prop :=
  (m, a) ∈ T.rows

/-- THEOREM 1: a finite table constructs the P89 raw discovery relation. -/
def toRawAtomicSupportDiscovery
    (T : RawAtomicSupportDiscoveryTable P M) :
    RawAtomicSupportDiscovery P M where
  represents := T.represents
  support_iff := by
    intro m a hrow
    exact T.row_support_iff m a hrow
  memory_total := T.memory_total
  semantic_total := T.semantic_total

/-! ## Consequences inherited from P89 -/

/-- THEOREM 2: under semantic atom independence, two rows for the same raw
memory atom must carry the same semantic label. -/
theorem row_label_unique_of_independent
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    {m : MemoryAtom} {a b : SemanticAtom}
    (ha : (m, a) ∈ T.rows) (hb : (m, b) ∈ T.rows) :
    a = b := by
  exact (T.toRawAtomicSupportDiscovery).represents_unique_of_independent
    hind ha hb

/-- THEOREM 3: a finite table constructs the raw classifier from P88. -/
noncomputable def toRawAtomicSupportClassifier
    (T : RawAtomicSupportDiscoveryTable P M) :
    RawAtomicSupportClassifier P M :=
  (T.toRawAtomicSupportDiscovery).toRawAtomicSupportClassifier

/-- THEOREM 4: under semantic atom independence, a finite table descends to the
P87 quotient classifier. -/
noncomputable def toQuotientAtomicSupportClassifier
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientAtomicSupportClassifier P M :=
  (T.toRawAtomicSupportDiscovery).toQuotientAtomicSupportClassifier hind

/-- THEOREM 5: a finite table gives singleton-failure query coverage after
quotienting. -/
theorem toSingletonFailureQueryCoverage
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    SingletonFailureQueryCoverage P M := by
  exact (T.toRawAtomicSupportDiscovery).toSingletonFailureQueryCoverage hind

/-- THEOREM 6: a finite table gives quotient support coverage. -/
theorem toQuotientSupportCoverage
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientSupportCoverage P M := by
  exact (T.toRawAtomicSupportDiscovery).toQuotientSupportCoverage hind

/-- THEOREM 7: a finite table constructs the strong quotient
memory/obstruction equivalence. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  (T.toRawAtomicSupportDiscovery).toGeneralMemoryObstructionEquivalence hind

/-- THEOREM 8: a finite table makes raw memory production exactly global
unsafety. -/
theorem raw_production_nonempty_iff_not_csafe
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  exact (T.toRawAtomicSupportDiscovery).raw_production_nonempty_iff_not_csafe
    hind x

end RawAtomicSupportDiscoveryTable

/-!
  Summary:
  - The runtime-facing bridge certificate can now be a finite rows table.
  - Each row must be support-checked, and the table must cover raw memory atoms
    and primitive semantic failure atoms.
  - Lean constructs the relation, raw classifier, quotient classifier,
    singleton-failure query coverage, quotient support coverage, and strong
    quotient memory/obstruction equivalence from that finite table.
-/
