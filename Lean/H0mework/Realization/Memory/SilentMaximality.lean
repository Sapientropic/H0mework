/-
  Proposition 36: obstruction structure corresponds to memory mechanisms.

  Proposition 32 established the pointwise isomorphism between canonical
  obstruction support and memory epistemic types.  The stronger question is
  whether the obstruction-side structure transports too:

    * maximality of `C_safe` ↔ maximal memory-silent / no-production domain;
    * presentation uniqueness ↔ memory epistemic presentation uniqueness;
    * graph H¹-like generator ↔ memory graph-obstruction production.

  This file proves those correspondences as theorems.  It still does not claim
  a full sheaf cohomology universal property; it transports the already-proved
  Prop-valued support/maximality/generator structure through the memory
  presentation.
-/

import H0mework.Realization.Observation.LocalMaximality
import H0mework.Realization.Reflexive.NonIdempotentWitness

/-! ## Maximality: C_safe as the greatest memory-silent domain -/

/-- A state is memory-silent when no memory epistemic type is produced there. -/
def MemorySilentAt {State : Type*}
    (P : CSafePredicates State) (x : State) : Prop :=
  forall m, MemoryProduction P x m -> False

/-- THEOREM 1: memory silence at a state is exactly membership in `C_safe`. -/
theorem memorySilentAt_iff_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    MemorySilentAt P x <-> CSafe P x := by
  constructor
  · intro hsilent
    have hsafeAtoms : SafeByAtoms (semanticObligationSemantics P) x := by
      intro a
      by_contra hfail
      have hm : MemoryProduction P x (semanticAtomToMemory a) :=
        (semanticFailure_iff_memoryProduction P x a).mp hfail
      exact hsilent (semanticAtomToMemory a) hm
    exact (semanticSafe_iff_csafe P x).mp hsafeAtoms
  · intro hsafe m hm
    have hsafeAtoms : SafeByAtoms (semanticObligationSemantics P) x :=
      (semanticSafe_iff_csafe P x).mpr hsafe
    exact hm (hsafeAtoms (memoryToSemanticAtom m))

/-- THEOREM 2: a state is unsafe exactly when some memory epistemic type is
    produced. -/
theorem memoryProduction_nonempty_iff_not_csafe {State : Type*}
    (P : CSafePredicates State) (x : State) :
    (exists m, MemoryProduction P x m) <-> (CSafe P x -> False) := by
  constructor
  · rintro ⟨m, hm⟩ hsafe
    exact ((memorySilentAt_iff_csafe P x).mpr hsafe) m hm
  · intro hunsafe
    rcases (semanticFailure_nonempty_iff_not_csafe P x).mpr hunsafe with
      ⟨a, ha⟩
    exact ⟨semanticAtomToMemory a,
      (semanticFailure_iff_memoryProduction P x a).mp ha⟩

/-- A domain is memory-silent when no point in it produces memory. -/
def MemorySilentDomain {State : Type*}
    (P : CSafePredicates State) (D : State -> Prop) : Prop :=
  forall x, D x -> MemorySilentAt P x

/-- THEOREM 3: any memory-silent domain is included in `C_safe`. -/
theorem memorySilent_subset_csafe {State : Type*}
    (P : CSafePredicates State) (D : State -> Prop)
    (hD : MemorySilentDomain P D) :
    PredSubset D (CSafe P) := by
  intro x hx
  exact (memorySilentAt_iff_csafe P x).mp (hD x hx)

/-- THEOREM 4: `C_safe` itself is memory-silent. -/
theorem cSafe_memorySilentDomain {State : Type*}
    (P : CSafePredicates State) :
    MemorySilentDomain P (CSafe P) := by
  intro x hx
  exact (memorySilentAt_iff_csafe P x).mpr hx

/-- `C_safe` viewed through memory: it is the greatest domain that produces no
    memory epistemic types. -/
def IsGreatestMemorySilentDomain {State : Type*}
    (P : CSafePredicates State) (C : State -> Prop) : Prop :=
  MemorySilentDomain P C /\
    forall D : State -> Prop, MemorySilentDomain P D -> PredSubset D C

/-- THEOREM 5: obstruction maximality transports to memory-production
    completeness: `C_safe` is the greatest memory-silent domain. -/
theorem cSafe_greatest_memorySilent_domain {State : Type*}
    (P : CSafePredicates State) :
    IsGreatestMemorySilentDomain P (CSafe P) := by
  constructor
  · exact cSafe_memorySilentDomain P
  · intro D hD
    exact memorySilent_subset_csafe P D hD

/-- THEOREM 6: any memory-silent extension of `C_safe` is equal to `C_safe`. -/
theorem memorySilent_extension_eq_csafe {State : Type*}
    (P : CSafePredicates State) (D : State -> Prop)
    (hcontains : PredSubset (CSafe P) D)
    (hsilent : MemorySilentDomain P D) :
    PredEq D (CSafe P) := by
  intro x
  constructor
  · exact memorySilent_subset_csafe P D hsilent x
  · exact hcontains x

/-! ## Uniqueness: memory presentations decode to the same support -/

/-- A presentation of memory production by an arbitrary representation `O`.
    It is canonical only if its decoded support is sound and complete with
    respect to `MemoryProduction`. -/
structure MemoryPresentation {State : Type*}
    (P : CSafePredicates State) (O : Type*) where
  classify : State -> O
  decodes : O -> MemoryEpistemicType -> Prop
  sound : forall x m, decodes (classify x) m -> MemoryProduction P x m
  complete : forall x m, MemoryProduction P x m -> decodes (classify x) m

/-- THEOREM 7: any sound-and-complete memory presentation decodes to exactly
    memory production support. -/
theorem memoryPresentation_unique_support {State O : Type*}
    (P : CSafePredicates State) (pres : MemoryPresentation P O)
    (x : State) (m : MemoryEpistemicType) :
    pres.decodes (pres.classify x) m <-> MemoryProduction P x m := by
  constructor
  · exact pres.sound x m
  · exact pres.complete x m

/-- THEOREM 8: any two sound-and-complete memory presentations are equivalent
    after decoding; representation choices add no canonical content. -/
theorem memoryPresentations_equivalent {State O₁ O₂ : Type*}
    (P : CSafePredicates State)
    (pres₁ : MemoryPresentation P O₁)
    (pres₂ : MemoryPresentation P O₂)
    (x : State) (m : MemoryEpistemicType) :
    pres₁.decodes (pres₁.classify x) m <->
      pres₂.decodes (pres₂.classify x) m := by
  calc
    pres₁.decodes (pres₁.classify x) m <-> MemoryProduction P x m :=
      memoryPresentation_unique_support P pres₁ x m
    _ <-> pres₂.decodes (pres₂.classify x) m :=
      (memoryPresentation_unique_support P pres₂ x m).symm

/-- The canonical memory presentation represents a state by its full memory
    production support predicate. -/
def canonicalMemoryPresentation {State : Type*}
    (P : CSafePredicates State) :
    MemoryPresentation P (MemoryEpistemicType -> Prop) where
  classify := fun x => MemoryProduction P x
  decodes := fun support m => support m
  sound := by
    intro _x _m h
    exact h
  complete := by
    intro _x _m h
    exact h

/-! ## Generators: graph H¹-like obstruction as memory production -/

/-- Memory-side version of global gluing failure support. -/
def MemoryGluingFailureSupport {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (m : MemoryEpistemicType) : Prop :=
  GluingFailureSupport PL PR PG glue l r (memoryToSemanticAtom m)

/-- THEOREM 9: memory-side gluing support is just semantic gluing support
    transported through the memory equivalence. -/
theorem memoryGluingFailureSupport_iff_semantic {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (m : MemoryEpistemicType) :
    MemoryGluingFailureSupport PL PR PG glue l r m <->
      GluingFailureSupport PL PR PG glue l r (memoryToSemanticAtom m) := by
  rfl

/-- THEOREM 10: the cross-critical-pair graph generator is exactly the memory
    graph-obstruction generator. -/
theorem graph_memory_gluing_failure_iff_h1_generator
    {Left Right Global : Type*}
    (PL : CSafePredicates Left) (PR : CSafePredicates Right)
    (PG : CSafePredicates Global) (glue : Left -> Right -> Global)
    (l : Left) (r : Right) (C : GraphGluingCocycle)
    (hL :
      semanticHolds PL SemanticAtom.graphConfluence l <-> C.leftConfluent)
    (hR :
      semanticHolds PR SemanticAtom.graphConfluence r <-> C.rightConfluent)
    (hG :
      semanticHolds PG SemanticAtom.graphConfluence (glue l r) <->
        C.globalConfluent) :
    MemoryGluingFailureSupport PL PR PG glue l r
      MemoryEpistemicType.graphObstruction <->
      GraphH1Generator C := by
  simpa [MemoryGluingFailureSupport, memoryToSemanticAtom] using
    graph_gluing_failure_iff_h1_generator PL PR PG glue l r C hL hR hG

/-!
  Summary:
  - `memorySilentAt_iff_csafe` and
    `cSafe_greatest_memorySilent_domain` transport obstruction maximality into
    memory-production completeness.
  - `memoryPresentation_unique_support` transports presentation uniqueness into
    the memory epistemic layer.
  - `graph_memory_gluing_failure_iff_h1_generator` identifies the graph
    cross-critical-pair generator as the memory `graphObstruction` production
    mechanism.
-/
