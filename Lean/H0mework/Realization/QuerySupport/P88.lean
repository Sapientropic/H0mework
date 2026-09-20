/-
  Proposition 88: raw memory-atom classifiers descend to quotient classifiers.

  Proposition 87 identified the exact runtime-facing certificate for the strong
  memory/obstruction bridge, but it still lived over `MemorySupportQuotient`.
  Real runtime code usually emits facts about raw memory atoms, not quotient
  classes.

  This file proves that a raw atomic support classifier is enough.  If each raw
  memory atom is classified by a primitive semantic failure query, and each
  primitive semantic failure has a raw representative, then semantic atom
  independence makes that classifier respect support equivalence.  Therefore it
  descends canonically to the quotient classifier from Proposition 87, which in
  turn supplies the P84/P85 bridge.
-/

import H0mework.Realization.QuerySupport.P87

/-! ## Raw runtime classifier certificate -/

/-- A classifier over raw memory atoms.

This is closer to a runtime table than `QuotientAtomicSupportClassifier`:
runtime can enumerate raw memory atom ids and assign each to a semantic atom.
The support iff fields are still mandatory; labels alone are not evidence. -/
structure RawAtomicSupportClassifier {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  supportAtom : MemoryAtom -> SemanticAtom
  support_iff :
    forall m x,
      M.produces x m <->
        BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery (supportAtom m)) x
  representative : SemanticAtom -> MemoryAtom
  representative_iff :
    forall a x,
      M.produces x (representative a) <->
        BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery a) x

namespace RawAtomicSupportClassifier

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 1: under semantic atom independence, a raw classifier cannot assign
different semantic atoms to support-equivalent memory atoms. -/
theorem supportAtom_respects_supportEquivalent
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    {m n : MemoryAtom}
    (heq : MemorySupportEquivalent M m n) :
    C.supportAtom m = C.supportAtom n := by
  apply semanticSupportExtensional_of_independent P hind
  intro x
  calc
    AtomFailure (semanticObligationSemantics P) x (C.supportAtom m)
        <-> BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery (C.supportAtom m)) x :=
      (singletonFailureQuery_eval_iff P (C.supportAtom m) x).symm
    _ <-> M.produces x m := (C.support_iff m x).symm
    _ <-> M.produces x n := heq x
    _ <-> BoolQuery.eval (semanticObligationSemantics P)
          (singletonFailureQuery (C.supportAtom n)) x :=
      C.support_iff n x
    _ <-> AtomFailure (semanticObligationSemantics P) x (C.supportAtom n) :=
      singletonFailureQuery_eval_iff P (C.supportAtom n) x

/-- THEOREM 2: a raw classifier descends to the quotient classifier required by
Proposition 87. -/
noncomputable def toQuotientAtomicSupportClassifier
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientAtomicSupportClassifier P M where
  supportAtom := fun q =>
    Quot.liftOn q C.supportAtom
      (by
        intro m n hmn
        exact C.supportAtom_respects_supportEquivalent hind hmn)
  support_iff := by
    intro q x
    refine Quot.inductionOn q ?_
    intro m
    exact C.support_iff m x
  representative := fun a =>
    memorySupportQuotientMk M (C.representative a)
  representative_iff := by
    intro a x
    exact (memorySupportQuotientProduces_mk M x (C.representative a)).trans
      (C.representative_iff a x)

/-- THEOREM 3: a raw classifier gives singleton-failure query coverage after
quotienting. -/
theorem toSingletonFailureQueryCoverage
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    SingletonFailureQueryCoverage P M := by
  exact (C.toQuotientAtomicSupportClassifier hind).toSingletonFailureQueryCoverage

/-- THEOREM 4: a raw classifier gives quotient support coverage. -/
theorem toQuotientSupportCoverage
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    QuotientSupportCoverage P M := by
  exact (C.toQuotientAtomicSupportClassifier hind).toQuotientSupportCoverage

/-- THEOREM 5: under semantic atom independence, a raw classifier constructs
the strong quotient memory/obstruction equivalence. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  QuotientAtomicSupportClassifier.toGeneralMemoryObstructionEquivalence
    (C.toQuotientAtomicSupportClassifier hind) hind

/-- THEOREM 6: with a raw classifier, quotient memory production is exactly
global unsafety. -/
theorem quotient_production_nonempty_iff_not_csafe
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      (CSafe P x -> False) := by
  exact QuotientAtomicSupportClassifier.production_nonempty_iff_not_csafe
    (C.toQuotientAtomicSupportClassifier hind) hind x

/-- THEOREM 7: raw memory production is exactly global unsafety, since the
support quotient preserves nonempty production. -/
theorem raw_production_nonempty_iff_not_csafe
    (C : RawAtomicSupportClassifier P M)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  calc
    (exists m, M.produces x m) <->
        exists q, (memorySupportQuotientContract M).produces x q :=
      (memorySupportQuotient_nonempty_iff_original M x).symm
    _ <-> (CSafe P x -> False) :=
      C.quotient_production_nonempty_iff_not_csafe hind x

end RawAtomicSupportClassifier

/-!
  Summary:
  - Runtime code can emit a raw memory-atom classifier.
  - Semantic atom independence proves that the classifier is stable under
    support quotienting; no extra quotient table is needed.
  - The raw classifier is therefore sufficient for the P87 classifier, the P85
    singleton-failure query coverage, and the P84 strong quotient
    memory/obstruction equivalence.
-/
