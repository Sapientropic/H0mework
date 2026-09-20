/-
  Proposition 15: the final-mile runtime contract.

  Proposition 14 proved that independence makes product-obligation coordinates
  irreducible.  This file packages the three remaining "last mile" obligations
  into explicit certificates:

    (a) runtime safety has product shape;
    (b) product facets are independent;
    (c) the lower failure-mode vocabulary is complete for those facets.

  Once those certificates are present, canonical obstructions are no longer a
  chosen taxonomy.  They are exactly the primitive singleton supports of the
  product semantics, and any taxonomy is only a complete presentation of that
  support.

  Remaining runtime debt: build these certificates for the concrete reducer,
  source/authority/freshness gates, graph rewriter, gauge boundary, contraction
  certificate, and Ω store.
-/

import H0mework.Realization.Observation.FailureSupport

/-! ## Product-shape runtime safety -/

/-- A runtime safety predicate has product shape when it is equivalent to
    satisfying every primitive obligation atom. -/
structure RuntimeProductContract (State Atom : Type*) where
  runtimeSafe : State → Prop
  semantics : ObligationSemantics State Atom
  product_shape : ∀ x, runtimeSafe x ↔ SafeByAtoms semantics x

/-- THEOREM 1: product shape makes runtime unsafety exactly nonempty atom
    failure support. -/
theorem runtimeUnsafe_iff_atomSupport_nonempty {State Atom : Type*}
    (C : RuntimeProductContract State Atom) (x : State) :
    ¬ C.runtimeSafe x ↔ ∃ a, AtomFailure C.semantics x a := by
  constructor
  · intro hunsafe
    exact (atomSupport_nonempty_iff_not_safe C.semantics x).mpr
      (fun hsafeAtoms => hunsafe ((C.product_shape x).mpr hsafeAtoms))
  · intro hsupport hsafe
    have hnotAtoms : ¬ SafeByAtoms C.semantics x :=
      (atomSupport_nonempty_iff_not_safe C.semantics x).mp hsupport
    exact hnotAtoms ((C.product_shape x).mp hsafe)

/-- A certified runtime contract adds independence of primitive facets. -/
structure CertifiedRuntimeContract (State Atom : Type*) where
  runtimeSafe : State → Prop
  semantics : ObligationSemantics State Atom
  product_shape : ∀ x, runtimeSafe x ↔ SafeByAtoms semantics x
  independent : AtomIndependent semantics

/-- Forget independence and keep only product shape. -/
def CertifiedRuntimeContract.toProduct {State Atom : Type*}
    (C : CertifiedRuntimeContract State Atom) :
    RuntimeProductContract State Atom where
  runtimeSafe := C.runtimeSafe
  semantics := C.semantics
  product_shape := C.product_shape

/-- THEOREM 2: in a certified runtime contract, every atom is primitive. -/
theorem certifiedRuntime_atoms_primitive {State Atom : Type*}
    [DecidableEq Atom]
    (C : CertifiedRuntimeContract State Atom) :
    ∀ a, PrimitiveFailureAtom C.semantics a := by
  exact primitiveAtom_of_independent C.semantics C.independent

/-- THEOREM 3: in a certified runtime contract, every primitive atom can occur
    as the sole failure of a genuinely unsafe runtime state. -/
theorem certifiedRuntime_singleton_unsafe {State Atom : Type*}
    [DecidableEq Atom]
    (C : CertifiedRuntimeContract State Atom) (a : Atom) :
    ∃ x, ¬ C.runtimeSafe x ∧ SingletonFailure C.semantics x a := by
  rcases singletonFailure_of_independent C.semantics C.independent a with ⟨x, hx⟩
  refine ⟨x, ?_, hx⟩
  intro hsafe
  exact singletonFailure_not_safe C.semantics hx ((C.product_shape x).mp hsafe)

/-! ## Completeness of a lower failure-mode vocabulary -/

/-- A lower failure-mode vocabulary is complete when it is equivalent to the
    primitive atom coordinates of the product semantics. -/
structure FailureModeBasis (State Atom Mode : Type*)
    (S : ObligationSemantics State Atom) where
  fails : Mode → State → Prop
  encode : Mode ≃ Atom
  failure_iff : ∀ x m, fails m x ↔ AtomFailure S x (encode m)

/-- A state has exactly one failed lower failure mode. -/
def SingletonModeFailure {State Atom Mode : Type*}
    {S : ObligationSemantics State Atom}
    (B : FailureModeBasis State Atom Mode S) (x : State) (m : Mode) : Prop :=
  B.fails m x ∧ ∀ m', B.fails m' x → m' = m

/-- A lower failure mode is primitive when it can appear as a singleton
    obstruction. -/
def PrimitiveFailureMode {State Atom Mode : Type*}
    {S : ObligationSemantics State Atom}
    (B : FailureModeBasis State Atom Mode S) (m : Mode) : Prop :=
  ∃ x, SingletonModeFailure B x m

/-- THEOREM 4: a complete lower failure-mode vocabulary has the same support
    as the atom semantics. -/
theorem modeFailure_nonempty_iff_atomSupport_nonempty {State Atom Mode : Type*}
    {S : ObligationSemantics State Atom}
    (B : FailureModeBasis State Atom Mode S) (x : State) :
    (∃ m, B.fails m x) ↔ ∃ a, AtomFailure S x a := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨B.encode m, (B.failure_iff x m).mp hm⟩
  · rintro ⟨a, ha⟩
    let m : Mode := B.encode.symm a
    have henc : B.encode m = a := by
      exact B.encode.apply_symm_apply a
    refine ⟨m, ?_⟩
    exact (B.failure_iff x m).mpr (by simpa [henc] using ha)

/-- THEOREM 5: product shape plus failure-mode completeness characterizes
    runtime unsafety without mentioning any hand-picked classifier. -/
theorem modeFailure_nonempty_iff_runtimeUnsafe {State Atom Mode : Type*}
    (C : RuntimeProductContract State Atom)
    (B : FailureModeBasis State Atom Mode C.semantics) (x : State) :
    (∃ m, B.fails m x) ↔ ¬ C.runtimeSafe x := by
  calc
    (∃ m, B.fails m x) ↔ ∃ a, AtomFailure C.semantics x a :=
      modeFailure_nonempty_iff_atomSupport_nonempty B x
    _ ↔ ¬ C.runtimeSafe x :=
      (runtimeUnsafe_iff_atomSupport_nonempty C x).symm

/-- THEOREM 6: independence plus failure-mode completeness forces every lower
    failure mode to be primitive. -/
theorem primitiveMode_of_certified_runtime {State Atom Mode : Type*}
    [DecidableEq Atom]
    (C : CertifiedRuntimeContract State Atom)
    (B : FailureModeBasis State Atom Mode C.semantics) :
    ∀ m, PrimitiveFailureMode B m := by
  intro m
  rcases singletonFailure_of_independent C.semantics C.independent (B.encode m) with
    ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · exact (B.failure_iff x m).mpr hx.1
  · intro m' hm'
    have hatomFail : AtomFailure C.semantics x (B.encode m') :=
      (B.failure_iff x m').mp hm'
    have henc : B.encode m' = B.encode m := hx.2 (B.encode m') hatomFail
    exact B.encode.injective henc

/-- THEOREM 7: the final-mile package.  Product shape, independence, and
    complete lower failure modes jointly imply:
      * lower failure support is exactly runtime unsafety;
      * every lower failure mode is primitive/irreducible. -/
theorem finalMile_obstructions_are_canonical {State Atom Mode : Type*}
    [DecidableEq Atom]
    (C : CertifiedRuntimeContract State Atom)
    (B : FailureModeBasis State Atom Mode C.semantics) :
    (∀ x, (∃ m, B.fails m x) ↔ ¬ C.runtimeSafe x) ∧
      (∀ m, PrimitiveFailureMode B m) := by
  constructor
  · intro x
    exact modeFailure_nonempty_iff_runtimeUnsafe C.toProduct B x
  · exact primitiveMode_of_certified_runtime C B

/-! ## AIppocampus taxonomy as one complete presentation -/

/-- `C_safe` as a runtime product contract over lower semantic atoms. -/
def cSafeRuntimeProductContract {State : Type*}
    (P : CSafePredicates State) :
    RuntimeProductContract State SemanticAtom where
  runtimeSafe := CSafe P
  semantics := semanticObligationSemantics P
  product_shape := by
    intro x
    exact (semanticSafe_iff_csafe P x).symm

/-- `C_safe` as a certified runtime contract when facet independence is
    supplied by the runtime/mechanism-faithfulness layer. -/
def cSafeCertifiedRuntimeContract {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    CertifiedRuntimeContract State SemanticAtom where
  runtimeSafe := CSafe P
  semantics := semanticObligationSemantics P
  product_shape := by
    intro x
    exact (semanticSafe_iff_csafe P x).symm
  independent := hind

/-- The reopen taxonomy is a complete failure-mode basis for lower semantic
    atoms.  This is where taxonomy enters: as presentation, not as source. -/
def taxonomyFailureBasis {State : Type*}
    (P : CSafePredicates State) :
    FailureModeBasis State SemanticAtom ReopenTaxonomy
      (semanticObligationSemantics P) where
  fails := fun r x => taxonomyWitness P x r
  encode :=
    { toFun := reopenToSemanticAtom
      invFun := semanticAtomToReopen
      left_inv := reopen_semantic_right_inverse
      right_inv := reopen_semantic_left_inverse }
  failure_iff := by
    intro x r
    exact taxonomyWitness_iff_semanticFailure P x r

/-- THEOREM 8: taxonomy support is exactly `¬ C_safe`, without using the
    first-failure classifier or decidability of facets. -/
theorem taxonomySupport_nonempty_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    (∃ r, taxonomyWitness P x r) ↔ ¬ CSafe P x := by
  exact modeFailure_nonempty_iff_runtimeUnsafe
    (cSafeRuntimeProductContract P) (taxonomyFailureBasis P) x

/-- THEOREM 9: if the lower semantic facets are independent, every taxonomy
    case is a primitive singleton obstruction. -/
theorem taxonomy_cases_primitive_of_independent {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    ∀ r, PrimitiveFailureMode (taxonomyFailureBasis P) r := by
  exact primitiveMode_of_certified_runtime
    (cSafeCertifiedRuntimeContract P hind) (taxonomyFailureBasis P)

/-- THEOREM 10: the AIppocampus final-mile package, conditional only on the
    runtime/mechanism-faithfulness proof of facet independence. -/
theorem cSafe_finalMile_obstructions_are_canonical {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    (∀ x, (∃ r, taxonomyWitness P x r) ↔ ¬ CSafe P x) ∧
      (∀ r, PrimitiveFailureMode (taxonomyFailureBasis P) r) := by
  exact finalMile_obstructions_are_canonical
    (cSafeCertifiedRuntimeContract P hind) (taxonomyFailureBasis P)

/-!
  Summary:
  - (a) product shape is the `RuntimeProductContract.product_shape` certificate;
  - (b) facet independence is the `CertifiedRuntimeContract.independent`
    certificate;
  - (c) facet completeness is the `FailureModeBasis` equivalence between lower
    failure modes and product atoms.

  With those three certificates, the obstruction vocabulary is forced: runtime
  unsafety is exactly nonempty lower failure support, and every lower failure
  mode is primitive/irreducible.  The reopen taxonomy is proved as a complete
  presentation of this support, not as the definition of obstruction.
-/
