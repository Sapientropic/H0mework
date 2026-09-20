/-
  Proposition 92: decidable finite support-table checks.

  Proposition 91 lowered the runtime bridge to exhaustive finite universes plus
  row-wise support proofs over those universes.  This file lowers the row proof
  itself to the shape of an executable checker:

      decide (raw memory production support iff primitive failure query) = true

  When the row support propositions are decidable, a runtime/fixture emitter can
  provide true Boolean decisions for every row/state pair.  Lean reconstructs
  the Proposition 91 finite exhaustive check, then inherits the P90/P89 bridge.
-/

import H0mework.Realization.QuerySupport.P91

/-! ## Decidable finite runtime check -/

/-- A finite exhaustive support-table check whose row support obligations are
provided as true Boolean decisions.

The `*_total` and coverage fields still remain explicit Prop-level
exhaustiveness obligations.  This module only lowers the local row iff checks
from proof fields to decidable checker output.
-/
structure DecidedFiniteRawAtomicSupportDiscoveryCheck {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  states : List State
  memoryAtoms : List MemoryAtom
  rows : List (MemoryAtom × SemanticAtom)
  state_total : forall x, x ∈ states
  memory_total : forall m, m ∈ memoryAtoms
  row_support_decidable :
    forall m a x,
      Decidable
        (M.produces x m <->
          BoolQuery.eval (semanticObligationSemantics P)
            (singletonFailureQuery a) x)
  row_support_decided :
    forall m a,
      (m, a) ∈ rows ->
        forall x,
          x ∈ states ->
            @decide
              (M.produces x m <->
                BoolQuery.eval (semanticObligationSemantics P)
                  (singletonFailureQuery a) x)
              (row_support_decidable m a x) = true
  memory_rows_cover :
    forall m, m ∈ memoryAtoms -> exists a, (m, a) ∈ rows
  semantic_rows_cover :
    forall a, a ∈ semanticAtomUniverse -> exists m, (m, a) ∈ rows

namespace DecidedFiniteRawAtomicSupportDiscoveryCheck

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 1: Boolean row checks reconstruct the P91 finite exhaustive check. -/
def toFiniteRawAtomicSupportDiscoveryCheck
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M) :
    FiniteRawAtomicSupportDiscoveryCheck P M where
  states := C.states
  memoryAtoms := C.memoryAtoms
  rows := C.rows
  state_total := C.state_total
  memory_total := C.memory_total
  row_support_checked := by
    intro m a hrow x hx
    exact @of_decide_eq_true
      (M.produces x m <->
        BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery a) x)
      (C.row_support_decidable m a x)
      (C.row_support_decided m a hrow x hx)
  memory_rows_cover := C.memory_rows_cover
  semantic_rows_cover := C.semantic_rows_cover

/-- THEOREM 2: Boolean finite checks reconstruct the P90 finite table. -/
def toRawAtomicSupportDiscoveryTable
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M) :
    RawAtomicSupportDiscoveryTable P M :=
  C.toFiniteRawAtomicSupportDiscoveryCheck.toRawAtomicSupportDiscoveryTable

/-- THEOREM 3: Boolean finite checks reconstruct the P89 raw discovery
relation. -/
def toRawAtomicSupportDiscovery
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M) :
    RawAtomicSupportDiscovery P M :=
  C.toFiniteRawAtomicSupportDiscoveryCheck.toRawAtomicSupportDiscovery

/-- THEOREM 4: under semantic atom independence, duplicate Boolean-check rows
for the same raw memory atom cannot carry different semantic labels. -/
theorem row_label_unique_of_independent
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    {m : MemoryAtom} {a b : SemanticAtom}
    (ha : (m, a) ∈ C.rows) (hb : (m, b) ∈ C.rows) :
    a = b := by
  exact C.toFiniteRawAtomicSupportDiscoveryCheck.row_label_unique_of_independent
    hind ha hb

/-- THEOREM 5: Boolean finite checks give singleton-failure query coverage
after quotienting. -/
theorem toSingletonFailureQueryCoverage
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    SingletonFailureQueryCoverage P M := by
  exact C.toFiniteRawAtomicSupportDiscoveryCheck.toSingletonFailureQueryCoverage
    hind

/-- THEOREM 6: Boolean finite checks give quotient support coverage. -/
theorem toQuotientSupportCoverage
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientSupportCoverage P M := by
  exact C.toFiniteRawAtomicSupportDiscoveryCheck.toQuotientSupportCoverage hind

/-- THEOREM 7: Boolean finite checks construct the strong quotient
memory/obstruction equivalence. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  C.toFiniteRawAtomicSupportDiscoveryCheck.toGeneralMemoryObstructionEquivalence
    hind

/-- THEOREM 8: Boolean finite checks make raw memory production exactly global
unsafety. -/
theorem raw_production_nonempty_iff_not_csafe
    (C : DecidedFiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  exact C.toFiniteRawAtomicSupportDiscoveryCheck.raw_production_nonempty_iff_not_csafe
    hind x

end DecidedFiniteRawAtomicSupportDiscoveryCheck

/-!
  Summary:
  - Row-wise support preservation can now enter Lean as executable Boolean
    decisions over an exhaustive finite state universe.
  - The remaining non-executable obligations are intentionally the global ones:
    state-universe exhaustion, memory-atom universe exhaustion, and table
    coverage.  Those are exactly the claims a runtime fixture must not make
    implicitly.
-/
