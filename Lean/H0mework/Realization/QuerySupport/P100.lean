/-
  Proposition 100: finite discovery tables generate the foundation bridge.

  Propositions 82-90 progressively lowered the memory/obstruction bridge from
  a hand-supplied equivalence to a finite raw support-discovery table.  The
  conclusions, however, were scattered: equivalence, nonempty production,
  greatest silent domain, support coverage, and presentation uniqueness lived
  as separate theorem calls.

  This file packages that line as one foundation certificate.  Given:

    * an independent memory-production contract;
    * semantic atom independence;
    * a finite table whose rows preserve support and cover both sides;

  Lean constructs the quotient memory/obstruction equivalence and the matching
  memory ontology consequences.  The atom equivalence is no longer a primitive
  input field: it is produced from the table through the support quotient.

  Boundary: the finite table is still a certificate.  This theorem does not
  prove that a particular runtime emits such a table, nor that the seven
  semantic atoms are product-complete for all possible agent-readable database
  obligations.
-/

import H0mework.Realization.QuerySupport.P90

/-! ## Generic memory presentation uniqueness -/

/-- A presentation of an independently specified memory-production contract by
an arbitrary representation `O`. -/
structure MemoryContractPresentation {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) (O : Type*) where
  classify : State -> O
  decodes : O -> MemoryAtom -> Prop
  sound : forall x m, decodes (classify x) m -> M.produces x m
  complete : forall x m, M.produces x m -> decodes (classify x) m

/-- THEOREM 1: any sound-and-complete memory-contract presentation decodes to
exactly the production support. -/
theorem memoryContractPresentation_unique_support
    {State MemoryAtom O : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (pres : MemoryContractPresentation M O)
    (x : State) (m : MemoryAtom) :
    pres.decodes (pres.classify x) m <-> M.produces x m := by
  constructor
  · exact pres.sound x m
  · exact pres.complete x m

/-- THEOREM 2: any two sound-and-complete memory-contract presentations are
equivalent after decoding. -/
theorem memoryContractPresentations_equivalent
    {State MemoryAtom O₁ O₂ : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (pres₁ : MemoryContractPresentation M O₁)
    (pres₂ : MemoryContractPresentation M O₂)
    (x : State) (m : MemoryAtom) :
    pres₁.decodes (pres₁.classify x) m <->
      pres₂.decodes (pres₂.classify x) m := by
  calc
    pres₁.decodes (pres₁.classify x) m <-> M.produces x m :=
      memoryContractPresentation_unique_support M pres₁ x m
    _ <-> pres₂.decodes (pres₂.classify x) m :=
      (memoryContractPresentation_unique_support M pres₂ x m).symm

/-- The canonical presentation represents a state by its full production
support. -/
def canonicalMemoryContractPresentation {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) :
    MemoryContractPresentation M (MemoryAtom -> Prop) where
  classify := fun x => M.produces x
  decodes := fun support m => support m
  sound := by
    intro _x _m h
    exact h
  complete := by
    intro _x _m h
    exact h

/-! ## Primitive memory atoms do not need decidable equality -/

/-- THEOREM 3: memory-atom independence makes every atom primitive.  This is
the same mathematical fact as Proposition 40's theorem, but without requiring
`DecidableEq`: the assignment `m' ↦ m' = m` is a Prop-valued assignment. -/
theorem primitiveMemoryProduction_of_independent_any
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) :
    forall m, PrimitiveMemoryProduction M m := by
  intro m
  let assignment : MemoryAtom -> Prop := fun m' => m' = m
  rcases M.independent assignment with ⟨x, hx⟩
  refine ⟨x, ?_, ?_⟩
  · exact (hx m).mpr rfl
  · intro m' hm'
    exact (hx m').mp hm'

/-! ## Foundation certificate generated from a finite discovery table -/

/-- The packed foundation bridge from obstruction algebra to memory ontology.

The memory side is quotient memory support: duplicate raw memory atoms with the
same production support have already been removed by construction. -/
structure FiniteDiscoveryFoundationCertificate {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  equivalence :
    GeneralMemoryObstructionEquivalence P
      (memorySupportQuotientContract M)
  raw_nonempty_iff_not_csafe :
    forall x, (exists m, M.produces x m) <-> (CSafe P x -> False)
  quotient_nonempty_iff_not_csafe :
    forall x,
      (exists q, (memorySupportQuotientContract M).produces x q) <->
        (CSafe P x -> False)
  cSafe_greatest_quotient_silent :
    IsGreatestMemoryContractSilentDomain
      (memorySupportQuotientContract M) (CSafe P)
  primitive_quotient_atoms :
    forall q, PrimitiveMemoryProduction (memorySupportQuotientContract M) q
  presentation_unique :
    forall {O : Type*}
      (pres :
        MemoryContractPresentation (memorySupportQuotientContract M) O)
      (x : State) (q : MemorySupportQuotient M),
        pres.decodes (pres.classify x) q <->
          (memorySupportQuotientContract M).produces x q
  presentations_equivalent :
    forall {O₁ O₂ : Type*}
      (pres₁ :
        MemoryContractPresentation (memorySupportQuotientContract M) O₁)
      (pres₂ :
        MemoryContractPresentation (memorySupportQuotientContract M) O₂)
      (x : State) (q : MemorySupportQuotient M),
        pres₁.decodes (pres₁.classify x) q <->
          pres₂.decodes (pres₂.classify x) q

namespace FiniteDiscoveryFoundationCertificate

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 4: the packed certificate's equivalence has the same production
support as semantic obstruction failure. -/
theorem produces_iff_obstruction
    (C : FiniteDiscoveryFoundationCertificate P M)
    (x : State) (q : MemorySupportQuotient M) :
    (memorySupportQuotientContract M).produces x q <->
      AtomFailure (semanticObligationSemantics P) x (C.equivalence.atomEquiv q) :=
  C.equivalence.produces_iff_obstruction x q

/-- THEOREM 5: the packed certificate's equivalence makes quotient silence
exactly `C_safe`. -/
theorem quotient_silent_iff_csafe
    (C : FiniteDiscoveryFoundationCertificate P M) (x : State) :
    (memorySupportQuotientContract M).memorySilent x <-> CSafe P x :=
  C.equivalence.silent_iff_csafe x

end FiniteDiscoveryFoundationCertificate

/-- THEOREM 6: a finite raw support-discovery table constructs the full
foundation certificate. -/
noncomputable def foundationCertificate_of_finiteDiscoveryTable
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    FiniteDiscoveryFoundationCertificate P M where
  equivalence := T.toGeneralMemoryObstructionEquivalence hind
  raw_nonempty_iff_not_csafe := by
    intro x
    exact T.raw_production_nonempty_iff_not_csafe hind x
  quotient_nonempty_iff_not_csafe := by
    intro x
    exact
      GeneralMemoryObstructionEquivalence.production_nonempty_iff_not_csafe
        (T.toGeneralMemoryObstructionEquivalence hind) x
  cSafe_greatest_quotient_silent :=
    GeneralMemoryObstructionEquivalence.cSafe_greatest_memory_silent_domain
      (T.toGeneralMemoryObstructionEquivalence hind)
  primitive_quotient_atoms :=
    primitiveMemoryProduction_of_independent_any
      (memorySupportQuotientContract M)
  presentation_unique := by
    intro O pres x q
    exact memoryContractPresentation_unique_support
      (memorySupportQuotientContract M) pres x q
  presentations_equivalent := by
    intro O₁ O₂ pres₁ pres₂ x q
    exact memoryContractPresentations_equivalent
      (memorySupportQuotientContract M) pres₁ pres₂ x q

/-!
  Summary:
  - A finite raw support-discovery table now yields one packed foundation
    certificate rather than a loose collection of bridge lemmas.
  - The certificate includes the discovered quotient atom equivalence, raw and
    quotient nonempty-production iff unsafety, greatest silent domain,
    primitive quotient memory atoms, and presentation uniqueness.
  - The remaining real obligation is external to this theorem: produce such a
    finite table for the concrete runtime and justify the seven semantic atoms
    as the intended product basis.
-/
