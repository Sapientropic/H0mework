/-
  Proposition 83: canonical support quotient for memory atoms.

  Proposition 82 made the memory/obstruction discovery relation canonical:
  representation is extensional support equality.  It left two concrete
  memory-side obligations:

    * support coverage against semantic obstruction atoms;
    * memory support extensionality.

  This file removes the second obligation by construction.  Any independent
  memory-production contract can be quotiented by "same production support at
  every state".  The quotient memory atoms are support-extensional by theorem,
  silence/nonempty production are preserved, and P82 can then be applied with
  only support coverage left as the real semantic obligation.

  Boundary: quotienting does not prove that the seven semantic atoms are a
  complete support basis.  It only says duplicate memory atoms with identical
  support carry no canonical content.
-/

import H0mework.Realization.QuerySupport.P82

/-! ## Support equivalence and quotient atoms -/

/-- Two memory atoms are equivalent when they have identical production support
at every state. -/
def MemorySupportEquivalent {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (m n : MemoryAtom) : Prop :=
  forall x, M.produces x m <-> M.produces x n

/-- Support equivalence is an equivalence relation. -/
theorem memorySupportEquivalent_equivalence
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) :
    Equivalence (MemorySupportEquivalent M) := by
  constructor
  · intro m x
    rfl
  · intro m n h x
    exact (h x).symm
  · intro m n k hmn hnk x
    exact (hmn x).trans (hnk x)

/-- The setoid that identifies memory atoms with the same production support. -/
def memorySupportSetoid {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) : Setoid MemoryAtom where
  r := MemorySupportEquivalent M
  iseqv := memorySupportEquivalent_equivalence M

/-- Canonical support quotient of memory atoms. -/
def MemorySupportQuotient {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) : Type _ :=
  Quot (memorySupportSetoid M)

/-- The quotient atom represented by a memory atom. -/
def memorySupportQuotientMk {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (m : MemoryAtom) : MemorySupportQuotient M :=
  Quot.mk (memorySupportSetoid M) m

/-- Production support lifted to quotient memory atoms. -/
def memorySupportQuotientProduces {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (x : State) (q : MemorySupportQuotient M) : Prop :=
  Quot.liftOn q
    (fun m => M.produces x m)
    (by
      intro m n h
      exact propext (h x))

/-- THEOREM 1: quotient production agrees with original production on
representatives. -/
theorem memorySupportQuotientProduces_mk
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom)
    (x : State) (m : MemoryAtom) :
    memorySupportQuotientProduces M x (memorySupportQuotientMk M m) <->
      M.produces x m := by
  rfl

/-! ## Quotient memory-production contract -/

/-- The memory contract whose atoms are support equivalence classes. -/
def memorySupportQuotientContract {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) :
    MemoryProductionContract State (MemorySupportQuotient M) where
  produces := memorySupportQuotientProduces M
  memorySilent := M.memorySilent
  product_shape := by
    intro x
    constructor
    · intro hsilent q hq
      refine Quot.inductionOn q ?_ hq
      intro m hm
      exact ((M.product_shape x).mp hsilent m hm)
    · intro hquot
      apply (M.product_shape x).mpr
      intro m hm
      exact hquot (memorySupportQuotientMk M m) hm
  independent := by
    intro assignment
    rcases M.independent
      (fun m => assignment (memorySupportQuotientMk M m)) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro q
    refine Quot.inductionOn q ?_
    intro m
    exact hx m

/-- THEOREM 2: quotient silence is exactly original silence. -/
theorem memorySupportQuotient_silent_iff_original
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) (x : State) :
    (memorySupportQuotientContract M).memorySilent x <-> M.memorySilent x := by
  rfl

/-- THEOREM 3: quotient nonempty production is exactly original nonempty
production. -/
theorem memorySupportQuotient_nonempty_iff_original
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      exists m, M.produces x m := by
  constructor
  · rintro ⟨q, hq⟩
    refine Quot.inductionOn q ?_ hq
    intro m hm
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨memorySupportQuotientMk M m, hm⟩

/-- THEOREM 4: the support quotient is support-extensional by construction. -/
theorem memorySupportQuotient_extensional
    {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) :
    MemorySupportExtensional (memorySupportQuotientContract M) := by
  intro q r hsame
  revert r hsame
  refine Quot.inductionOn q ?_
  intro m r hsame
  revert hsame
  refine Quot.inductionOn r ?_
  intro n hsame
  apply Quot.sound
  intro x
  exact hsame x

/-! ## Applying P82 after quotienting -/

/-- THEOREM 5: after quotienting memory atoms by support, semantic independence
plus support coverage is enough to get P82's canonical support-equality
discovery certificate. -/
theorem supportEqualityDiscovery_of_quotient_and_semantic_independent
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (memory_total :
      forall q : MemorySupportQuotient M,
        exists a,
          MemorySemanticSupportEq P (memorySupportQuotientContract M) q a)
    (semantic_total :
      forall a : SemanticAtom,
        exists q : MemorySupportQuotient M,
          MemorySemanticSupportEq P (memorySupportQuotientContract M) q a) :
    SupportEqualityDiscovery P (memorySupportQuotientContract M) := by
  exact supportEqualityDiscovery_of_semantic_independent
    P (memorySupportQuotientContract M) hind memory_total semantic_total
    (memorySupportQuotient_extensional M)

/-- THEOREM 6: the quotient discovery certificate gives nonempty quotient
memory production exactly at unsafe states. -/
theorem quotient_production_nonempty_iff_not_csafe
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (memory_total :
      forall q : MemorySupportQuotient M,
        exists a,
          MemorySemanticSupportEq P (memorySupportQuotientContract M) q a)
    (semantic_total :
      forall a : SemanticAtom,
        exists q : MemorySupportQuotient M,
          MemorySemanticSupportEq P (memorySupportQuotientContract M) q a)
    (x : State) :
    (exists q, (memorySupportQuotientContract M).produces x q) <->
      (CSafe P x -> False) := by
  exact
    (supportEqualityDiscovery_of_quotient_and_semantic_independent
      P M hind memory_total semantic_total).production_nonempty_iff_not_csafe x

/-!
  Summary:
  - Memory support quotienting is canonical: it identifies exactly those memory
    atoms that no state can distinguish by production support.
  - The quotient preserves silence and nonempty production.
  - The quotient is support-extensional, so P82 no longer needs memory
    extensionality as an external certificate after quotienting.
  - What remains is support coverage: every quotient memory support must match
    a semantic obstruction support, and every semantic obstruction support must
    be represented by some quotient memory support.
-/
