/-
  Proposition 82: support equality canonically discovers memory/obstruction atoms.

  Proposition 66 lowered the memory/obstruction equivalence assumption from a
  primitive atom equivalence to a support-discovery relation.  This file lowers
  it once more.  The relation is no longer arbitrary:

      a memory atom represents a semantic obstruction atom
      iff they have the same production/failure support at every state.

  If every memory atom and every semantic atom has such a support match, and
  memory atoms are separated by support, Lean constructs the P66 discovery
  relation and therefore the generalized memory/obstruction equivalence.

  The semantic side's support separation is not assumed when the obstruction
  semantics is atom-independent: it is proved below.  Thus the remaining
  nontrivial runtime/theory obligation is memory-side support extensionality
  plus total support coverage.
-/

import H0mework.Realization.Memory.ObstructionEquivalence

/-! ## Extensional support equality -/

/-- A memory atom and a semantic atom have the same support when production of
the memory atom is equivalent, at every state, to failure of the semantic atom.
-/
def MemorySemanticSupportEq {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (m : MemoryAtom) (a : SemanticAtom) : Prop :=
  forall x, M.produces x m <->
    AtomFailure (semanticObligationSemantics P) x a

/-- Memory atoms are support-extensional if identical production support forces
atom equality. -/
def MemorySupportExtensional {State MemoryAtom : Type*}
    (M : MemoryProductionContract State MemoryAtom) : Prop :=
  forall m n, (forall x, M.produces x m <-> M.produces x n) -> m = n

/-- Semantic atoms are support-extensional if identical failure support forces
atom equality. -/
def SemanticSupportExtensional {State : Type*}
    (P : CSafePredicates State) : Prop :=
  forall a b,
    (forall x,
      AtomFailure (semanticObligationSemantics P) x a <->
        AtomFailure (semanticObligationSemantics P) x b) -> a = b

/-- A support-equality discovery certificate: support equality is total on both
sides, and supports separate atoms on both sides. -/
structure SupportEqualityDiscovery {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  memory_total : forall m, exists a, MemorySemanticSupportEq P M m a
  semantic_total : forall a, exists m, MemorySemanticSupportEq P M m a
  memory_extensional : MemorySupportExtensional M
  semantic_extensional : SemanticSupportExtensional P

namespace SupportEqualityDiscovery

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 1: support-equality discovery canonically supplies the P66
`MemorySupportDiscovery` relation.  The relation is exactly support equality. -/
def toMemorySupportDiscovery
    (D : SupportEqualityDiscovery P M) :
    MemorySupportDiscovery P M where
  represents := MemorySemanticSupportEq P M
  support_iff := by
    intro m a h x
    exact h x
  memory_total := D.memory_total
  semantic_total := D.semantic_total
  memory_unique := by
    intro m a b hma hmb
    apply D.semantic_extensional a b
    intro x
    exact (hma x).symm.trans (hmb x)
  semantic_unique := by
    intro a m n hma hna
    apply D.memory_extensional m n
    intro x
    exact (hma x).trans (hna x).symm

/-- THEOREM 2: in the constructed discovery relation, representation is exactly
extensional support equality. -/
theorem represents_iff_supportEq
    (D : SupportEqualityDiscovery P M) (m : MemoryAtom) (a : SemanticAtom) :
    (D.toMemorySupportDiscovery).represents m a <->
      MemorySemanticSupportEq P M m a := by
  rfl

/-- THEOREM 3: support-equality discovery constructs the generalized
memory/obstruction equivalence from Proposition 66. -/
noncomputable def toGeneralMemoryObstructionEquivalence
    (D : SupportEqualityDiscovery P M) :
    GeneralMemoryObstructionEquivalence P M :=
  (D.toMemorySupportDiscovery).toGeneralMemoryObstructionEquivalence

/-- THEOREM 4: support-equality discovery gives nonempty production exactly at
unsafe states. -/
theorem production_nonempty_iff_not_csafe
    (D : SupportEqualityDiscovery P M) (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) :=
  MemorySupportDiscovery.discovered_production_nonempty_iff_not_csafe
    D.toMemorySupportDiscovery x

/-- THEOREM 5: support-equality discovery gives the greatest memory-silent
domain property. -/
theorem cSafe_greatest_memory_silent_domain
    (D : SupportEqualityDiscovery P M) :
    IsGreatestMemoryContractSilentDomain M (CSafe P) :=
  MemorySupportDiscovery.discovered_cSafe_greatest_memory_silent_domain
    D.toMemorySupportDiscovery

end SupportEqualityDiscovery

/-! ## Semantic support extensionality from independence -/

/-- THEOREM 6: in an independent product semantics, failure support separates
semantic atoms.  No two distinct primitive coordinates fail on exactly the same
states. -/
theorem atomFailure_support_extensional_of_independent {State Atom : Type*}
    [DecidableEq Atom]
    (S : ObligationSemantics State Atom)
    (hind : AtomIndependent S) :
    forall a b,
      (forall x, AtomFailure S x a <-> AtomFailure S x b) -> a = b := by
  intro a b hsame
  by_contra hne
  rcases singletonFailure_of_independent S hind a with ⟨x, hx⟩
  have hfailB : AtomFailure S x b := (hsame x).mp hx.1
  have hb_eq_a : b = a := hx.2 b hfailB
  exact hne hb_eq_a.symm

/-- THEOREM 7: if the lower semantic facets are independent, semantic support
extensionality follows automatically for `C_safe`. -/
theorem semanticSupportExtensional_of_independent {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    SemanticSupportExtensional P := by
  exact atomFailure_support_extensional_of_independent
    (semanticObligationSemantics P) hind

/-! ## Building the canonical discovery certificate with only memory-side
extensionality plus support coverage. -/

/-- THEOREM 8: under semantic independence, a memory contract whose atoms are
support-covered and support-extensional canonically discovers the
memory/obstruction equivalence. -/
theorem supportEqualityDiscovery_of_semantic_independent
    {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom)
    (hind : AtomIndependent (semanticObligationSemantics P))
    (memory_total : forall m, exists a, MemorySemanticSupportEq P M m a)
    (semantic_total : forall a, exists m, MemorySemanticSupportEq P M m a)
    (memory_extensional : MemorySupportExtensional M) :
    SupportEqualityDiscovery P M := by
  exact
    { memory_total := memory_total
      semantic_total := semantic_total
      memory_extensional := memory_extensional
      semantic_extensional := semanticSupportExtensional_of_independent P hind }

/-!
  Summary:
  - The discovery relation can be made canonical: representation is extensional
    support equality, not a hand-picked map.
  - Semantic-side support separation follows from atom independence.
  - The remaining concrete obligation is precise: the memory side must provide
    total support coverage and memory support extensionality.
-/
