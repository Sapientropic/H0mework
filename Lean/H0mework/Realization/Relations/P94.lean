/-
  Proposition 94: semantic-product projection bridge.

  Proposition 93 closed the Lean side of the concrete `2^7` semantic Boolean
  slice.  The remaining mechanism-faithfulness question is not another finite
  fixture: it is whether a real runtime state can be projected into that slice
  without changing the seven lower safety obligations or the memory-production
  support.

  This file states that bridge as a reusable theorem.  If a runtime supplies:

    * a projection `State -> SemanticBoolState`;
    * preservation of each lower semantic atom through that projection;
    * surjectivity onto the semantic slice, for the independence certificate;
    * memory production as the pullback of the semantic Boolean memory support;

  then Lean constructs the raw atomic support discovery relation and inherits
  the P89/P88/P87 memory/obstruction bridge.  The runtime still has to supply
  those projection proofs; but the shape is no longer implicit.
-/

import H0mework.Realization.Relations.P93

/-! ## Boolean semantic slice independence -/

/-- Convert an arbitrary truth assignment over the seven semantic atoms into
the concrete Boolean semantic-product state. -/
noncomputable def semanticBoolStateFromAssignment
    (assignment : SemanticAtom → Prop) : SemanticBoolState := by
  classical
  exact
    { sourceReachability :=
        if assignment SemanticAtom.sourceReachability then true else false
      authorityMonotonicity :=
        if assignment SemanticAtom.authorityMonotonicity then true else false
      graphConfluence :=
        if assignment SemanticAtom.graphConfluence then true else false
      gaugeInvariance :=
        if assignment SemanticAtom.gaugeInvariance then true else false
      contractionCertification :=
        if assignment SemanticAtom.contractionCertification then true else false
      omegaGluing :=
        if assignment SemanticAtom.omegaGluing then true else false
      freshnessValidity :=
        if assignment SemanticAtom.freshnessValidity then true else false }

/-- THEOREM 1: the concrete Boolean semantic-product state realizes exactly the
truth assignment it was built from. -/
theorem semanticBoolStateFromAssignment_holds
    (assignment : SemanticAtom → Prop) (a : SemanticAtom) :
    (semanticObligationSemantics semanticBoolPredicates).holds a
        (semanticBoolStateFromAssignment assignment) <->
      assignment a := by
  classical
  cases a <;>
    simp [semanticBoolStateFromAssignment, semanticObligationSemantics,
      semanticHolds, semanticBoolPredicates]

/-- THEOREM 2: the concrete Boolean semantic-product slice is atom-independent. -/
theorem semanticBoolPredicates_independent :
    AtomIndependent (semanticObligationSemantics semanticBoolPredicates) where
  realize := by
    intro assignment
    exact ⟨semanticBoolStateFromAssignment assignment,
      semanticBoolStateFromAssignment_holds assignment⟩

/-! ## Projection from a runtime state into the semantic Boolean slice -/

/-- A runtime state projects faithfully into the concrete semantic Boolean
slice when each lower semantic atom is exactly the pullback of its Boolean
coordinate, and every Boolean semantic state is realized by some runtime state.

The surjectivity field is deliberately explicit: without it the projection can
preserve truth values for existing runtime states while still being too narrow
to prove atom independence. -/
structure SemanticBoolProjectionCertificate {State : Type*}
    (P : CSafePredicates State) where
  project : State → SemanticBoolState
  atom_iff :
    ∀ x a,
      (semanticObligationSemantics P).holds a x <->
        (semanticObligationSemantics semanticBoolPredicates).holds a (project x)
  state_surjective :
    ∀ y : SemanticBoolState, ∃ x : State, project x = y

namespace SemanticBoolProjectionCertificate

variable {State : Type*}
variable {P : CSafePredicates State}

/-- THEOREM 3: primitive atom failure is preserved by a faithful semantic
projection. -/
theorem atomFailure_iff_project
    (C : SemanticBoolProjectionCertificate P)
    (x : State) (a : SemanticAtom) :
    AtomFailure (semanticObligationSemantics P) x a <->
      AtomFailure (semanticObligationSemantics semanticBoolPredicates)
        (C.project x) a := by
  constructor
  · intro hfail hproject
    exact hfail ((C.atom_iff x a).mpr hproject)
  · intro hfail hx
    exact hfail ((C.atom_iff x a).mp hx)

/-- THEOREM 4: `C_safe` is exactly the pullback of the Boolean semantic
product's `C_safe`. -/
theorem cSafe_iff_project
    (C : SemanticBoolProjectionCertificate P) (x : State) :
    CSafe P x <-> CSafe semanticBoolPredicates (C.project x) := by
  calc
    CSafe P x <->
        SafeByAtoms (semanticObligationSemantics P) x :=
      (semanticSafe_iff_csafe P x).symm
    _ <->
        SafeByAtoms (semanticObligationSemantics semanticBoolPredicates)
          (C.project x) := by
      constructor
      · intro hsafe a
        exact (C.atom_iff x a).mp (hsafe a)
      · intro hsafe a
        exact (C.atom_iff x a).mpr (hsafe a)
    _ <->
        CSafe semanticBoolPredicates (C.project x) :=
      semanticSafe_iff_csafe semanticBoolPredicates (C.project x)

/-- THEOREM 5: a surjective faithful projection transports the Boolean slice's
atom independence back to the runtime state space. -/
theorem atomIndependent
    (C : SemanticBoolProjectionCertificate P) :
    AtomIndependent (semanticObligationSemantics P) where
  realize := by
    intro assignment
    rcases C.state_surjective (semanticBoolStateFromAssignment assignment) with
      ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro a
    calc
      (semanticObligationSemantics P).holds a x <->
          (semanticObligationSemantics semanticBoolPredicates).holds a
            (C.project x) := C.atom_iff x a
      _ <->
          (semanticObligationSemantics semanticBoolPredicates).holds a
            (semanticBoolStateFromAssignment assignment) := by
        rw [hx]
      _ <-> assignment a :=
          semanticBoolStateFromAssignment_holds assignment a

end SemanticBoolProjectionCertificate

/-! ## Memory support as pullback of the semantic Boolean support -/

/-- A runtime memory-production layer with raw atoms already identified as the
seven semantic atoms.  Production must be the pullback of the concrete Boolean
semantic memory support along a faithful semantic projection.

This is the exact theorem-side shape of the runtime certificate left open by
Proposition 93.  A runtime with richer raw memory atoms should first emit a
P89/P90 table, or prove that its raw atoms quotient to these semantic atoms.
-/
structure SemanticBoolMemoryPullback {State : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State SemanticAtom) where
  projection : SemanticBoolProjectionCertificate P
  memory_pullback :
    ∀ x a,
      M.produces x a <->
        semanticBoolMemoryContract.produces (projection.project x) a

namespace SemanticBoolMemoryPullback

variable {State : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State SemanticAtom}

/-- THEOREM 6: memory pullback gives a raw atomic support discovery relation
with the diagonal table `semantic atom ↔ semantic atom`. -/
noncomputable def toRawAtomicSupportDiscovery
    (C : SemanticBoolMemoryPullback P M) :
    RawAtomicSupportDiscovery P M where
  represents := fun m a => m = a
  support_iff := by
    intro m a hrow x
    subst a
    calc
      M.produces x m <->
          semanticBoolMemoryContract.produces (C.projection.project x) m :=
        C.memory_pullback x m
      _ <-> semanticBoolValue (C.projection.project x) m = false :=
        Iff.rfl
      _ <->
          AtomFailure (semanticObligationSemantics semanticBoolPredicates)
            (C.projection.project x) m :=
        (semanticBoolFailure_iff_value_false (C.projection.project x) m).symm
      _ <->
          AtomFailure (semanticObligationSemantics P) x m :=
        (C.projection.atomFailure_iff_project x m).symm
      _ <->
          BoolQuery.eval (semanticObligationSemantics P)
            (singletonFailureQuery m) x :=
        (singletonFailureQuery_eval_iff P m x).symm
  memory_total := by
    intro m
    exact ⟨m, rfl⟩
  semantic_total := by
    intro a
    exact ⟨a, rfl⟩

/-- THEOREM 7: the pullback certificate yields singleton-failure query coverage
after quotienting. -/
theorem toSingletonFailureQueryCoverage
    (C : SemanticBoolMemoryPullback P M) :
    SingletonFailureQueryCoverage P M := by
  exact C.toRawAtomicSupportDiscovery.toSingletonFailureQueryCoverage
    C.projection.atomIndependent

/-- THEOREM 8: the pullback certificate yields quotient support coverage. -/
theorem toQuotientSupportCoverage
    (C : SemanticBoolMemoryPullback P M) :
    QuotientSupportCoverage P M := by
  exact C.toRawAtomicSupportDiscovery.toQuotientSupportCoverage
    C.projection.atomIndependent

/-- THEOREM 9: the pullback certificate constructs the strong quotient
memory/obstruction equivalence. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (C : SemanticBoolMemoryPullback P M) :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M) :=
  C.toRawAtomicSupportDiscovery.toGeneralMemoryObstructionEquivalence
    C.projection.atomIndependent

/-- THEOREM 10: with a faithful semantic-memory pullback, raw memory production
is exactly global unsafety. -/
theorem raw_production_nonempty_iff_not_csafe
    (C : SemanticBoolMemoryPullback P M) (x : State) :
    (∃ a, M.produces x a) <-> (CSafe P x -> False) := by
  exact C.toRawAtomicSupportDiscovery.raw_production_nonempty_iff_not_csafe
    C.projection.atomIndependent x

end SemanticBoolMemoryPullback

/-!
  Summary:
  - Proposition 93's finite semantic Boolean slice is now a reusable target for
    runtime mechanism-faithfulness.
  - A real runtime no longer has to mimic the finite fixture.  It can instead
    prove that its own state space projects onto the Boolean semantic-product
    slice and that memory production is the pullback of primitive semantic
    failure support.
  - The remaining runtime work is exactly to emit or prove the projection,
    atom pullback, surjectivity, and memory pullback certificates for concrete
    production states.
-/
