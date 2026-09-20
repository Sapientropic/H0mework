/-
  Proposition 32: obstruction support as memory epistemic ontology.

  Propositions 10-15 prove the canonical obstruction side:
    * failed semantic atoms are the primitive obstruction support;
    * reopen taxonomy is a lossless presentation of those atoms;
    * singleton failures are the minimal/primitive generators.

  This file gives the missing "memory" reading explicitly.  A memory
  epistemic type is not an additional classifier; it is another lossless
  presentation of the same lower semantic atoms.  Therefore memory production
  is uniquely determined by obstruction support, and conversely every memory
  production type decodes back to the same obstruction atom.

  Boundary: this is an isomorphism for the already-proved product-obligation
  support object.  It is not a sheaf cohomology theorem and does not add a
  group/cochain structure to `GluingFailureSupport`.
-/

import H0mework.Realization.Observation.FailureSupport

/-! ## Memory epistemic types as a presentation of semantic obstruction atoms -/

/-- Epistemic memory-production types.  These are the memory-side readings of
    the lower semantic obstruction atoms. -/
inductive MemoryEpistemicType where
  | sourceGap
  | authorityBoundary
  | graphObstruction
  | gaugeBoundaryLeak
  | contractionUncertified
  | omegaGluingConflict
  | freshnessInvalid
  deriving DecidableEq, Repr

/-- Encode lower semantic obstruction atoms as memory epistemic types. -/
def semanticAtomToMemory : SemanticAtom -> MemoryEpistemicType
  | SemanticAtom.sourceReachability => MemoryEpistemicType.sourceGap
  | SemanticAtom.authorityMonotonicity => MemoryEpistemicType.authorityBoundary
  | SemanticAtom.graphConfluence => MemoryEpistemicType.graphObstruction
  | SemanticAtom.gaugeInvariance => MemoryEpistemicType.gaugeBoundaryLeak
  | SemanticAtom.contractionCertification => MemoryEpistemicType.contractionUncertified
  | SemanticAtom.omegaGluing => MemoryEpistemicType.omegaGluingConflict
  | SemanticAtom.freshnessValidity => MemoryEpistemicType.freshnessInvalid

/-- Decode memory epistemic types back to lower semantic atoms. -/
def memoryToSemanticAtom : MemoryEpistemicType -> SemanticAtom
  | MemoryEpistemicType.sourceGap => SemanticAtom.sourceReachability
  | MemoryEpistemicType.authorityBoundary => SemanticAtom.authorityMonotonicity
  | MemoryEpistemicType.graphObstruction => SemanticAtom.graphConfluence
  | MemoryEpistemicType.gaugeBoundaryLeak => SemanticAtom.gaugeInvariance
  | MemoryEpistemicType.contractionUncertified => SemanticAtom.contractionCertification
  | MemoryEpistemicType.omegaGluingConflict => SemanticAtom.omegaGluing
  | MemoryEpistemicType.freshnessInvalid => SemanticAtom.freshnessValidity

/-- THEOREM 1: semantic obstruction atom -> memory type -> semantic atom is
    identity. -/
theorem memory_semantic_left_inverse :
    forall a, memoryToSemanticAtom (semanticAtomToMemory a) = a := by
  intro a
  cases a <;> rfl

/-- THEOREM 2: memory type -> semantic atom -> memory type is identity. -/
theorem memory_semantic_right_inverse :
    forall m, semanticAtomToMemory (memoryToSemanticAtom m) = m := by
  intro m
  cases m <;> rfl

/-- The semantic obstruction atoms and memory epistemic types are equivalent
    presentations of the same primitive support object. -/
def semanticMemoryEquiv : SemanticAtom ≃ MemoryEpistemicType where
  toFun := semanticAtomToMemory
  invFun := memoryToSemanticAtom
  left_inv := memory_semantic_left_inverse
  right_inv := memory_semantic_right_inverse

/-- Memory production support at a state: the corresponding semantic
    obstruction atom failed. -/
def MemoryProduction {State : Type*}
    (P : CSafePredicates State) (x : State) (m : MemoryEpistemicType) : Prop :=
  AtomFailure (semanticObligationSemantics P) x (memoryToSemanticAtom m)

/-- THEOREM 3: memory production is exactly semantic obstruction failure under
    the memory presentation. -/
theorem memoryProduction_iff_semanticFailure {State : Type*}
    (P : CSafePredicates State) (x : State) (m : MemoryEpistemicType) :
    MemoryProduction P x m <->
      AtomFailure (semanticObligationSemantics P) x (memoryToSemanticAtom m) := by
  rfl

/-- THEOREM 4: semantic obstruction failure is exactly memory production under
    the semantic-to-memory presentation. -/
theorem semanticFailure_iff_memoryProduction {State : Type*}
    (P : CSafePredicates State) (x : State) (a : SemanticAtom) :
    AtomFailure (semanticObligationSemantics P) x a <->
      MemoryProduction P x (semanticAtomToMemory a) := by
  cases a <;> rfl

/-- Reopen taxonomy cases map to memory epistemic types through semantic atoms. -/
def reopenToMemory (r : ReopenTaxonomy) : MemoryEpistemicType :=
  semanticAtomToMemory (reopenToSemanticAtom r)

/-- Memory epistemic types map back to reopen taxonomy cases. -/
def memoryToReopen (m : MemoryEpistemicType) : ReopenTaxonomy :=
  semanticAtomToReopen (memoryToSemanticAtom m)

/-- THEOREM 5: reopen taxonomy -> memory type -> reopen taxonomy is identity. -/
theorem memory_reopen_left_inverse :
    forall r, memoryToReopen (reopenToMemory r) = r := by
  intro r
  unfold memoryToReopen reopenToMemory
  rw [memory_semantic_left_inverse]
  exact reopen_semantic_right_inverse r

/-- THEOREM 6: memory type -> reopen taxonomy -> memory type is identity. -/
theorem memory_reopen_right_inverse :
    forall m, reopenToMemory (memoryToReopen m) = m := by
  intro m
  unfold reopenToMemory memoryToReopen
  rw [reopen_semantic_left_inverse]
  exact memory_semantic_right_inverse m

/-- The reopen taxonomy and memory epistemic types are equivalent presentations
    once both are decoded through semantic obstruction atoms. -/
def reopenMemoryEquiv : ReopenTaxonomy ≃ MemoryEpistemicType where
  toFun := reopenToMemory
  invFun := memoryToReopen
  left_inv := memory_reopen_left_inverse
  right_inv := memory_reopen_right_inverse

/-- THEOREM 7: canonical reopen support is exactly memory production support
    under the reopen-to-memory isomorphism. -/
theorem canonicalSupport_iff_memoryProduction {State : Type*}
    (P : CSafePredicates State) (x : State) (r : ReopenTaxonomy) :
    canonicalReopenSupport P x r <->
      MemoryProduction P x (reopenToMemory r) := by
  have h := taxonomyWitness_iff_semanticFailure P x r
  simpa [canonicalReopenSupport, MemoryProduction, reopenToMemory,
    memory_semantic_left_inverse] using h

/-- THEOREM 8: memory production support is exactly canonical reopen support
    under the memory-to-reopen isomorphism. -/
theorem memoryProduction_iff_canonicalSupport {State : Type*}
    (P : CSafePredicates State) (x : State) (m : MemoryEpistemicType) :
    MemoryProduction P x m <->
      canonicalReopenSupport P x (memoryToReopen m) := by
  have h := (taxonomyWitness_iff_semanticFailure P x
    (semanticAtomToReopen (memoryToSemanticAtom m))).symm
  simpa [MemoryProduction, canonicalReopenSupport, memoryToReopen,
    reopen_semantic_left_inverse] using h

/-! ## Minimal memory production types -/

/-- A memory type is the unique produced memory type at a state. -/
def MemorySingletonProduction {State : Type*}
    (P : CSafePredicates State) (x : State) (m : MemoryEpistemicType) : Prop :=
  MemoryProduction P x m /\ forall m', MemoryProduction P x m' -> m' = m

/-- THEOREM 9: singleton semantic obstruction failures transport to singleton
    memory production types. -/
theorem semanticSingleton_iff_memorySingleton {State : Type*}
    (P : CSafePredicates State) (x : State) (m : MemoryEpistemicType) :
    SemanticSingletonFailure P x (memoryToSemanticAtom m) <->
      MemorySingletonProduction P x m := by
  constructor
  · intro h
    constructor
    · exact h.1
    · intro m' hm'
      have ha : memoryToSemanticAtom m' = memoryToSemanticAtom m := h.2 _ hm'
      calc
        m' = semanticAtomToMemory (memoryToSemanticAtom m') := by
          exact (memory_semantic_right_inverse m').symm
        _ = semanticAtomToMemory (memoryToSemanticAtom m) := by
          rw [ha]
        _ = m := memory_semantic_right_inverse m
  · intro h
    constructor
    · exact h.1
    · intro a ha
      let m' := semanticAtomToMemory a
      have hm' : MemoryProduction P x m' :=
        (semanticFailure_iff_memoryProduction P x a).mp ha
      have hm_eq : m' = m := h.2 m' hm'
      calc
        a = memoryToSemanticAtom (semanticAtomToMemory a) := by
          exact (memory_semantic_left_inverse a).symm
        _ = memoryToSemanticAtom m := by
          have hdecode : memoryToSemanticAtom m' = memoryToSemanticAtom m :=
            congrArg memoryToSemanticAtom hm_eq
          simpa [m'] using hdecode

/-- THEOREM 10: if lower semantic obligations are independent, every memory
    epistemic type is forced as a singleton/minimal memory production type. -/
theorem memorySingleton_of_semantic_independent {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (m : MemoryEpistemicType) :
    exists x, MemorySingletonProduction P x m := by
  classical
  rcases singletonFailure_of_independent
    (semanticObligationSemantics P) hind (memoryToSemanticAtom m) with ⟨x, hx⟩
  exact ⟨x, (semanticSingleton_iff_memorySingleton P x m).mp hx⟩

/-!
  Summary:
  - `MemoryEpistemicType` is a lossless presentation of the same semantic
    obstruction atoms used by the canonical support object.
  - Canonical reopen obstruction support and memory production support are
    isomorphic (`canonicalSupport_iff_memoryProduction` and its inverse).
  - Singleton/minimal obstruction generators transport to singleton/minimal
    memory production types.

  This is the formal version of "a gluing/obstruction failure is memory" for
  the currently proved support object: the memory ontology is uniquely
  determined by the obstruction atom, not chosen independently.
-/
