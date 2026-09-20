/-
  Proposition 43: the canonical independent memory contract constructs its
  memory-obstruction equivalence.

  Proposition 40 deliberately left `MemoryObstructionEquivalence` as an input
  certificate: an arbitrary independently specified memory-production contract
  should not be identified with obstruction support by fiat.

  This file closes the constructible canonical case.  If the memory contract is
  the canonical one whose productions are exactly `MemoryProduction P`, then
  the equivalence certificate is not an extra assumption; it is built by Lean.
  The only remaining assumption is the one already required by the independent
  contract shape: lower semantic atom independence, needed to realize every
  memory-production truth assignment.
-/

import H0mework.Realization.Memory.IndependentProduction
import H0mework.Realization.Reflexive.TruthTable

/-! ## Canonical independent memory-production contract -/

/-- The canonical memory-production contract induced by the already-proved
memory ontology.  Its `produces` predicate is the canonical
`MemoryProduction`, and its silence predicate is `C_safe`.

The independence field is exactly the lower semantic atom-independence
certificate transported through the memory/semantic isomorphism. -/
noncomputable def canonicalMemoryProductionContract {State : Type*}
    (P : CSafePredicates State)
    (hind : AtomIndependent (semanticObligationSemantics P)) :
    MemoryProductionContract State MemoryEpistemicType where
  produces := MemoryProduction P
  memorySilent := CSafe P
  product_shape := by
    intro x
    exact (memorySilentAt_iff_csafe P x).symm
  independent := by
    classical
    intro assignment
    let semanticAssignment : SemanticAtom -> Prop :=
      fun a => ¬ assignment (semanticAtomToMemory a)
    rcases hind.realize semanticAssignment with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro m
    have hholds :
        (semanticObligationSemantics P).holds (memoryToSemanticAtom m) x ↔
          ¬ assignment m := by
      have hraw := hx (memoryToSemanticAtom m)
      simpa [semanticAssignment, memory_semantic_right_inverse] using hraw
    constructor
    · intro hprod
      by_contra hnot
      exact hprod (hholds.mpr hnot)
    · intro hm hholdsNow
      exact (hholds.mp hholdsNow) hm

namespace CanonicalMemoryProductionContract

variable {State : Type*}
variable (P : CSafePredicates State)
variable (hind : AtomIndependent (semanticObligationSemantics P))

/-- THEOREM 1: the canonical contract's production predicate is exactly the
canonical memory-production support. -/
theorem produces_iff_memoryProduction (x : State) (m : MemoryEpistemicType) :
    (canonicalMemoryProductionContract P hind).produces x m <->
      MemoryProduction P x m := by
  rfl

/-- THEOREM 2: the canonical contract's silence predicate is exactly `C_safe`. -/
theorem silent_iff_csafe (x : State) :
    (canonicalMemoryProductionContract P hind).memorySilent x <-> CSafe P x := by
  rfl

/-- THEOREM 3: for the canonical memory contract, the
`MemoryObstructionEquivalence` certificate is constructed, not assumed. -/
theorem memoryObstructionEquivalence :
    MemoryObstructionEquivalence P (canonicalMemoryProductionContract P hind) := by
  constructor
  · intro x
    rfl
  · intro x m
    rfl

/-- THEOREM 4: the canonical contract inherits the full independent
memory/obstruction correspondence without taking equivalence as an external
input. -/
theorem independent_correspondence :
    (forall x,
      (exists m, (canonicalMemoryProductionContract P hind).produces x m) <->
        (CSafe P x -> False)) /\
      IsGreatestMemoryContractSilentDomain
        (canonicalMemoryProductionContract P hind) (CSafe P) /\
      (forall m,
        PrimitiveMemoryProduction
          (canonicalMemoryProductionContract P hind) m) := by
  exact independent_memory_obstruction_correspondence P
    (canonicalMemoryProductionContract P hind)
    (memoryObstructionEquivalence P hind)

/-- THEOREM 5: in the canonical independent contract, every memory epistemic
type is primitive as a production coordinate. -/
theorem every_memory_type_primitive :
    forall m,
      PrimitiveMemoryProduction
        (canonicalMemoryProductionContract P hind) m := by
  exact (independent_correspondence P hind).2.2

/-- THEOREM 6: non-silence in the canonical independent contract is exactly
canonical unsafe obstruction support. -/
theorem production_nonempty_iff_not_csafe (x : State) :
    (exists m, (canonicalMemoryProductionContract P hind).produces x m) <->
      (CSafe P x -> False) := by
  exact (independent_correspondence P hind).1 x

end CanonicalMemoryProductionContract

/-!
  Boundary:
  - This removes the equivalence assumption only for the canonical memory
    contract induced by `MemoryProduction P`.
  - A real runtime memory layer is still not allowed to claim this theorem
    unless it supplies the mechanism-faithfulness proof that its concrete
    `produces` predicate is this canonical one, plus the required atom
    independence / coverage certificates.
-/
