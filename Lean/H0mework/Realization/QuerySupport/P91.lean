/-
  Proposition 91: finite exhaustive support-table checks.

  Proposition 90 made the runtime-facing bridge a finite table, but each row
  still carried a global support-iff proof over every state.  This file lowers
  that obligation to the certificate shape a finite runtime harness can emit:

    * an exhaustive finite list of states for the checked domain;
    * an exhaustive finite list of raw memory atoms;
    * finite rows `(memory atom, semantic atom)`;
    * row-wise support checks over the state list;
    * coverage checks for raw memory atoms and the fixed semantic atom universe.

  If the emitted finite universes are genuinely exhaustive, Lean reconstructs
  the Proposition 90 table and all downstream memory/obstruction bridges.
-/

import H0mework.Realization.QuerySupport.P90

/-! ## Fixed finite semantic atom universe -/

/-- The declared lower semantic atom universe.  Runtime certificates should not
invent taxonomy cases; they cover this fixed product-coordinate vocabulary. -/
def semanticAtomUniverse : List SemanticAtom :=
  [ SemanticAtom.sourceReachability
  , SemanticAtom.authorityMonotonicity
  , SemanticAtom.graphConfluence
  , SemanticAtom.gaugeInvariance
  , SemanticAtom.contractionCertification
  , SemanticAtom.omegaGluing
  , SemanticAtom.freshnessValidity
  ]

/-- THEOREM 1: the declared semantic atom universe is complete. -/
theorem semanticAtom_mem_universe (a : SemanticAtom) :
    a ∈ semanticAtomUniverse := by
  cases a <;> simp [semanticAtomUniverse]

/-! ## Finite exhaustive runtime check -/

/-- A finite exhaustive support-table check.

`states` and `memoryAtoms` are not merely samples.  Their `*_total` fields are
the explicit exhaustion obligations that prevent fixture coverage from being
silently promoted into a full runtime claim.
-/
structure FiniteRawAtomicSupportDiscoveryCheck {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  states : List State
  memoryAtoms : List MemoryAtom
  rows : List (MemoryAtom × SemanticAtom)
  state_total : forall x, x ∈ states
  memory_total : forall m, m ∈ memoryAtoms
  row_support_checked :
    forall m a,
      (m, a) ∈ rows ->
        forall x,
          x ∈ states ->
            (M.produces x m <->
              BoolQuery.eval (semanticObligationSemantics P)
                (singletonFailureQuery a) x)
  memory_rows_cover :
    forall m, m ∈ memoryAtoms -> exists a, (m, a) ∈ rows
  semantic_rows_cover :
    forall a, a ∈ semanticAtomUniverse -> exists m, (m, a) ∈ rows

namespace FiniteRawAtomicSupportDiscoveryCheck

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 2: an exhaustive finite check reconstructs the finite P90 table. -/
def toRawAtomicSupportDiscoveryTable
    (C : FiniteRawAtomicSupportDiscoveryCheck P M) :
    RawAtomicSupportDiscoveryTable P M where
  rows := C.rows
  row_support_iff := by
    intro m a hrow x
    exact C.row_support_checked m a hrow x (C.state_total x)
  memory_total := by
    intro m
    exact C.memory_rows_cover m (C.memory_total m)
  semantic_total := by
    intro a
    exact C.semantic_rows_cover a (semanticAtom_mem_universe a)

/-! ## Consequences inherited from P90 -/

/-- THEOREM 3: an exhaustive finite check constructs the P89 raw discovery
relation. -/
def toRawAtomicSupportDiscovery
    (C : FiniteRawAtomicSupportDiscoveryCheck P M) :
    RawAtomicSupportDiscovery P M :=
  C.toRawAtomicSupportDiscoveryTable.toRawAtomicSupportDiscovery

/-- THEOREM 4: under semantic atom independence, duplicate finite-table rows for
the same raw memory atom cannot carry different semantic labels. -/
theorem row_label_unique_of_independent
    (C : FiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    {m : MemoryAtom} {a b : SemanticAtom}
    (ha : (m, a) ∈ C.rows) (hb : (m, b) ∈ C.rows) :
    a = b := by
  exact C.toRawAtomicSupportDiscoveryTable.row_label_unique_of_independent
    hind ha hb

/-- THEOREM 5: an exhaustive finite check gives singleton-failure query
coverage after quotienting. -/
theorem toSingletonFailureQueryCoverage
    (C : FiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    SingletonFailureQueryCoverage P M := by
  exact C.toRawAtomicSupportDiscoveryTable.toSingletonFailureQueryCoverage hind

/-- THEOREM 6: an exhaustive finite check gives quotient support coverage. -/
theorem toQuotientSupportCoverage
    (C : FiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientSupportCoverage P M := by
  exact C.toRawAtomicSupportDiscoveryTable.toQuotientSupportCoverage hind

/-- THEOREM 7: an exhaustive finite check constructs the strong quotient
memory/obstruction equivalence. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (C : FiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  C.toRawAtomicSupportDiscoveryTable.toGeneralMemoryObstructionEquivalence hind

/-- THEOREM 8: an exhaustive finite check makes raw memory production exactly
global unsafety. -/
theorem raw_production_nonempty_iff_not_csafe
    (C : FiniteRawAtomicSupportDiscoveryCheck P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  exact C.toRawAtomicSupportDiscoveryTable.raw_production_nonempty_iff_not_csafe
    hind x

end FiniteRawAtomicSupportDiscoveryCheck

/-!
  Summary:
  - The runtime-facing bridge can now be emitted as finite universes plus
    row-wise checks over those universes.
  - The semantic atom side is fixed by `semanticAtomUniverse`; runtime output
    covers it, it does not redefine it.
  - Exhaustiveness of the state and memory universes remains explicit.  Without
    those totality fields, the certificate is a fixture/sample report, not a
    full support bridge.
-/
