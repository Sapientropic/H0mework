/-
  Proposition 133: packed obstruction-memory ontology isomorphism.

  Earlier propositions prove the pieces:

  * P66 constructs memory/semantic atom equivalence from support discovery;
  * P83 quotients duplicate memory atoms by production support;
  * P100 packages a finite discovery table into a foundation certificate;
  * P101/P104 show a semantic-memory pullback and structure-determined
    seven-facet system generate that certificate.

  This file names the total object those pieces were converging toward:

      obstruction algebra = memory ontology

  for the current quotient-support fragment.  The theorem is not a new
  classifier and not a sheaf cohomology universal property.  It is the maximal
  Lean-level foundation certificate currently justified: once a finite support
  discovery table or P94/P104 pullback is supplied, memory atoms, production,
  silence, maximality, primitive support, and presentation uniqueness are all
  forced by the semantic obstruction algebra.
-/

import H0mework.Realization.QuerySupport.P104

/-! ## The packed ontology isomorphism object -/

/-- The current strongest Lean object for "obstruction algebra = memory
ontology".

The memory side is quotient memory support, so duplicate raw memory atoms with
the same production support carry no extra ontology.  The semantic side is the
seven primitive `SemanticAtom` obstruction basis.
-/
structure ObstructionMemoryOntologyIso {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  atomEquiv : MemorySupportQuotient M ≃ SemanticAtom
  produces_iff_obstruction :
    forall x q,
      (memorySupportQuotientContract M).produces x q <->
        AtomFailure (semanticObligationSemantics P) x (atomEquiv q)
  raw_nonempty_iff_not_csafe :
    forall x, (exists m, M.produces x m) <-> (CSafe P x -> False)
  quotient_nonempty_iff_not_csafe :
    forall x,
      (exists q, (memorySupportQuotientContract M).produces x q) <->
        (CSafe P x -> False)
  quotient_silent_iff_csafe :
    forall x, (memorySupportQuotientContract M).memorySilent x <-> CSafe P x
  greatest_quotient_silent :
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

namespace ObstructionMemoryOntologyIso

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 1: the ontology iso exposes semantic obstruction support as exactly
quotient memory production. -/
theorem support_iff
    (I : ObstructionMemoryOntologyIso P M)
    (x : State) (q : MemorySupportQuotient M) :
    (memorySupportQuotientContract M).produces x q <->
      AtomFailure (semanticObligationSemantics P) x (I.atomEquiv q) :=
  I.produces_iff_obstruction x q

/-- THEOREM 2: memory silence in the quotient ontology is exactly `C_safe`. -/
theorem silent_iff_safe
    (I : ObstructionMemoryOntologyIso P M) (x : State) :
    (memorySupportQuotientContract M).memorySilent x <-> CSafe P x :=
  I.quotient_silent_iff_csafe x

/-- THEOREM 3: the quotient ontology produces some memory exactly off
`C_safe`. -/
theorem production_nonempty_iff_unsafe
    (I : ObstructionMemoryOntologyIso P M) (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      (CSafe P x -> False) :=
  I.quotient_nonempty_iff_not_csafe x

/-- THEOREM 4: any sound-and-complete presentation of the quotient memory
ontology has no additional canonical content beyond production support. -/
theorem presentation_forced
    (I : ObstructionMemoryOntologyIso P M)
    {O : Type*}
    (pres : MemoryContractPresentation (memorySupportQuotientContract M) O)
    (x : State) (q : MemorySupportQuotient M) :
    pres.decodes (pres.classify x) q <->
      AtomFailure (semanticObligationSemantics P) x (I.atomEquiv q) := by
  calc
    pres.decodes (pres.classify x) q <->
        (memorySupportQuotientContract M).produces x q :=
      memoryContractPresentation_unique_support
        (memorySupportQuotientContract M) pres x q
    _ <-> AtomFailure (semanticObligationSemantics P) x (I.atomEquiv q) :=
      I.produces_iff_obstruction x q

end ObstructionMemoryOntologyIso

/-! ## Constructors from existing foundation certificates -/

/-- THEOREM 5: a P100 finite discovery foundation certificate generates the
packed obstruction-memory ontology isomorphism. -/
def ObstructionMemoryOntologyIso.ofFoundationCertificate
    {State MemoryAtom : Type*}
    {P : CSafePredicates State}
    {M : MemoryProductionContract State MemoryAtom}
    (C : FiniteDiscoveryFoundationCertificate P M) :
    ObstructionMemoryOntologyIso P M where
  atomEquiv := C.equivalence.atomEquiv
  produces_iff_obstruction := C.equivalence.produces_iff_obstruction
  raw_nonempty_iff_not_csafe := C.raw_nonempty_iff_not_csafe
  quotient_nonempty_iff_not_csafe := C.quotient_nonempty_iff_not_csafe
  quotient_silent_iff_csafe := C.equivalence.silent_iff_csafe
  greatest_quotient_silent := C.cSafe_greatest_quotient_silent
  primitive_quotient_atoms := C.primitive_quotient_atoms
  presentation_unique := C.presentation_unique
  presentations_equivalent := C.presentations_equivalent

/-- THEOREM 6: a finite raw support-discovery table directly generates the
packed obstruction-memory ontology isomorphism. -/
noncomputable def ObstructionMemoryOntologyIso.ofFiniteDiscoveryTable
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (T : RawAtomicSupportDiscoveryTable P M)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    ObstructionMemoryOntologyIso P M :=
  ObstructionMemoryOntologyIso.ofFoundationCertificate
    (foundationCertificate_of_finiteDiscoveryTable P M T hind)

namespace SemanticBoolMemoryPullback

variable {State : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State SemanticAtom}

/-- THEOREM 7: a P94 semantic-memory pullback directly generates the packed
obstruction-memory ontology isomorphism. -/
noncomputable def toObstructionMemoryOntologyIso
    (C : SemanticBoolMemoryPullback P M) :
    ObstructionMemoryOntologyIso P M :=
  ObstructionMemoryOntologyIso.ofFoundationCertificate
    C.toFiniteDiscoveryFoundationCertificate

end SemanticBoolMemoryPullback

namespace StructureDeterminedSevenFacetSystem

variable {State : Type*}

/-- THEOREM 8: a structure-determined seven-facet system carries the packed
obstruction-memory ontology isomorphism forced by its pullback structure. -/
noncomputable def ontologyIso
    (S : StructureDeterminedSevenFacetSystem State) :
    ObstructionMemoryOntologyIso S.predicates S.memory :=
  ObstructionMemoryOntologyIso.ofFoundationCertificate
    S.foundationCertificate

/-- THEOREM 9: in a structure-determined system, quotient memory production is
exactly the semantic obstruction support selected by the forced atom
equivalence. -/
theorem ontologyIso_support_iff
    (S : StructureDeterminedSevenFacetSystem State)
    (x : State) (q : MemorySupportQuotient S.memory) :
    (memorySupportQuotientContract S.memory).produces x q <->
      AtomFailure (semanticObligationSemantics S.predicates) x
        ((S.ontologyIso).atomEquiv q) :=
  S.ontologyIso.support_iff x q

/-- THEOREM 10: in a structure-determined system, quotient memory silence is
exactly the global `C_safe` predicate. -/
theorem ontologyIso_silent_iff_csafe
    (S : StructureDeterminedSevenFacetSystem State) (x : State) :
    (memorySupportQuotientContract S.memory).memorySilent x <->
      CSafe S.predicates x :=
  S.ontologyIso.silent_iff_safe x

end StructureDeterminedSevenFacetSystem

/-!
  Summary:
  - `ObstructionMemoryOntologyIso` is now the named total certificate for the
    current formal claim that obstruction algebra determines memory ontology.
  - It combines atom equivalence, support iff, raw/quotient nonempty production,
    `C_safe` silence, greatest silent domain, primitive quotient atoms, and
    presentation uniqueness.
  - P100 finite discovery tables, P94 semantic-memory pullbacks, and P104
    structure-determined seven-facet systems all construct this same object.

  Remaining boundary:
  - This still lives at the support-quotient / seven-semantic-atom level.
    It is not a proof that no eighth safety facet exists outside the declared
    projection-visible family, and it is not a full sheaf cohomology universal
    property for `GluingFailureSupport`.
-/
