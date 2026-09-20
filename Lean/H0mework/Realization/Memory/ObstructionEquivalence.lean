/-
  Proposition 66: discovering the memory/obstruction equivalence from support.

  Proposition 40 introduced an independent memory-production contract, but its
  connection to obstruction semantics was still supplied as a
  `MemoryObstructionEquivalence` certificate.  That certificate already moved
  beyond a mere `memoryToSemanticAtom` relabeling, but the atom equivalence was
  still assumed.

  This file lowers that assumption.  A runtime/theory may instead supply a
  support discovery relation:

      memory atom m represents semantic obstruction atom a

  together with totality and uniqueness on both sides.  From that relation Lean
  constructs the atom equivalence `MemoryAtom ≃ SemanticAtom`, proves support
  preservation, and derives the usual silence / nonempty-production /
  greatest-domain consequences.

  This is still conditional: the discovery relation is a certificate.  But the
  equivalence is no longer a primitive field of the contract; it is constructed
  from an independently stated support relation.
-/

import H0mework.Realization.Fields.Family
import H0mework.Realization.Memory.IndependentProduction

/-! ## General memory/obstruction equivalence -/

/-- A generalized obstruction equivalence for an independently named memory
atom vocabulary.  Unlike `MemoryObstructionEquivalence`, the memory atom type is
not fixed to `MemoryEpistemicType`. -/
structure GeneralMemoryObstructionEquivalence {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  atomEquiv : MemoryAtom ≃ SemanticAtom
  silent_iff_csafe : forall x, M.memorySilent x <-> CSafe P x
  produces_iff_obstruction :
    forall x m, M.produces x m <->
      AtomFailure (semanticObligationSemantics P) x (atomEquiv m)

namespace GeneralMemoryObstructionEquivalence

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

/-- THEOREM 1: under a generalized equivalence, nonempty memory production is
exactly global unsafety at that state. -/
theorem production_nonempty_iff_not_csafe
    (E : GeneralMemoryObstructionEquivalence P M) (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) := by
  constructor
  · intro hprod hsafe
    have hsilent : M.memorySilent x := (E.silent_iff_csafe x).mpr hsafe
    exact (memoryContract_production_nonempty_iff_not_silent M x).mp hprod
      hsilent
  · intro hnotSafe
    exact (memoryContract_production_nonempty_iff_not_silent M x).mpr
      (fun hsilent => hnotSafe ((E.silent_iff_csafe x).mp hsilent))

/-- THEOREM 2: `C_safe` is the greatest domain silent for the independently
named memory atom vocabulary. -/
theorem cSafe_greatest_memory_silent_domain
    (E : GeneralMemoryObstructionEquivalence P M) :
    IsGreatestMemoryContractSilentDomain M (CSafe P) := by
  constructor
  · intro x hx
    exact (E.silent_iff_csafe x).mpr hx
  · intro D hD x hx
    exact (E.silent_iff_csafe x).mp (hD x hx)

/-- THEOREM 3: if the independent memory contract is atom-independent, then
every independently named memory atom is primitive. -/
theorem primitive_memory_atoms_of_independent
    [DecidableEq MemoryAtom]
    (_E : GeneralMemoryObstructionEquivalence P M) :
    forall m, PrimitiveMemoryProduction M m := by
  intro m
  exact primitiveMemoryProduction_of_independent M m

end GeneralMemoryObstructionEquivalence

/-! ## Support discovery relation -/

/-- A support discovery relation between an independently specified memory
contract and semantic obstruction atoms.

`represents m a` is intentionally separate from any predeclared function.  The
four totality/uniqueness laws say that this relation is a bijective
correspondence, while `support_iff` says it preserves the actual production
support. -/
structure MemorySupportDiscovery {State MemoryAtom : Type*}
    (P : CSafePredicates State)
    (M : MemoryProductionContract State MemoryAtom) where
  represents : MemoryAtom -> SemanticAtom -> Prop
  support_iff :
    forall m a,
      represents m a ->
        forall x, M.produces x m <->
          AtomFailure (semanticObligationSemantics P) x a
  memory_total : forall m, exists a, represents m a
  semantic_total : forall a, exists m, represents m a
  memory_unique :
    forall m a b, represents m a -> represents m b -> a = b
  semantic_unique :
    forall a m n, represents m a -> represents n a -> m = n

namespace MemorySupportDiscovery

variable {State MemoryAtom : Type*}
variable {P : CSafePredicates State}
variable {M : MemoryProductionContract State MemoryAtom}

noncomputable section

/-- The semantic atom represented by a memory atom, constructed from the
support-discovery relation. -/
def toSemantic (D : MemorySupportDiscovery P M) (m : MemoryAtom) :
    SemanticAtom :=
  Classical.choose (D.memory_total m)

/-- The memory atom representing a semantic atom, constructed from the same
support-discovery relation. -/
def toMemory (D : MemorySupportDiscovery P M) (a : SemanticAtom) :
    MemoryAtom :=
  Classical.choose (D.semantic_total a)

/-- THEOREM 4: the chosen `toSemantic` is supported by the discovery relation.
-/
theorem represents_toSemantic
    (D : MemorySupportDiscovery P M) (m : MemoryAtom) :
    D.represents m (D.toSemantic m) := by
  exact Classical.choose_spec (D.memory_total m)

/-- THEOREM 5: the chosen `toMemory` is supported by the discovery relation. -/
theorem represents_toMemory
    (D : MemorySupportDiscovery P M) (a : SemanticAtom) :
    D.represents (D.toMemory a) a := by
  exact Classical.choose_spec (D.semantic_total a)

/-- THEOREM 6: support discovery constructs a memory/semantic atom equivalence.
This is the key step: the equivalence is not an input field; it is derived from
totality plus uniqueness of the support relation. -/
def discoveredAtomEquiv
    (D : MemorySupportDiscovery P M) : MemoryAtom ≃ SemanticAtom where
  toFun := D.toSemantic
  invFun := D.toMemory
  left_inv := by
    intro m
    exact D.semantic_unique (D.toSemantic m)
      (D.toMemory (D.toSemantic m)) m
      (D.represents_toMemory (D.toSemantic m))
      (D.represents_toSemantic m)
  right_inv := by
    intro a
    exact D.memory_unique (D.toMemory a)
      (D.toSemantic (D.toMemory a)) a
      (D.represents_toSemantic (D.toMemory a))
      (D.represents_toMemory a)

/-- THEOREM 7: the discovered atom equivalence preserves production support. -/
theorem discoveredAtomEquiv_support_iff
    (D : MemorySupportDiscovery P M) (x : State) (m : MemoryAtom) :
    M.produces x m <->
      AtomFailure (semanticObligationSemantics P) x
        (D.discoveredAtomEquiv m) := by
  exact D.support_iff m (D.toSemantic m) (D.represents_toSemantic m) x

/-- THEOREM 8: the discovered relation also lets `C_safe` characterize memory
silence. -/
theorem discovered_silent_iff_csafe
    (D : MemorySupportDiscovery P M) (x : State) :
    M.memorySilent x <-> CSafe P x := by
  constructor
  · intro hsilent
    have hsafeAtoms : SafeByAtoms (semanticObligationSemantics P) x := by
      intro a
      by_contra hfail
      let m := D.toMemory a
      have hmRep : D.represents m a := by
        exact D.represents_toMemory a
      have hprod : M.produces x m :=
        (D.support_iff m a hmRep x).mpr hfail
      exact ((M.product_shape x).mp hsilent m hprod)
    exact (semanticSafe_iff_csafe P x).mp hsafeAtoms
  · intro hsafe
    have hsafeAtoms : SafeByAtoms (semanticObligationSemantics P) x :=
      (semanticSafe_iff_csafe P x).mpr hsafe
    apply (M.product_shape x).mpr
    intro m hprod
    have hmRep : D.represents m (D.toSemantic m) :=
      D.represents_toSemantic m
    have hfail :
        AtomFailure (semanticObligationSemantics P) x (D.toSemantic m) :=
      (D.support_iff m (D.toSemantic m) hmRep x).mp hprod
    exact hfail (hsafeAtoms (D.toSemantic m))

/-- THEOREM 9: a support discovery relation constructs the full generalized
memory-obstruction equivalence. -/
def toGeneralMemoryObstructionEquivalence
    (D : MemorySupportDiscovery P M) :
    GeneralMemoryObstructionEquivalence P M where
  atomEquiv := D.discoveredAtomEquiv
  silent_iff_csafe := D.discovered_silent_iff_csafe
  produces_iff_obstruction := D.discoveredAtomEquiv_support_iff

/-- THEOREM 10: support discovery gives nonempty-production iff unsafety. -/
theorem discovered_production_nonempty_iff_not_csafe
    (D : MemorySupportDiscovery P M) (x : State) :
    (exists m, M.produces x m) <-> (CSafe P x -> False) :=
  GeneralMemoryObstructionEquivalence.production_nonempty_iff_not_csafe
    (D.toGeneralMemoryObstructionEquivalence) x

/-- THEOREM 11: support discovery gives the greatest memory-silent-domain
property. -/
theorem discovered_cSafe_greatest_memory_silent_domain
    (D : MemorySupportDiscovery P M) :
    IsGreatestMemoryContractSilentDomain M (CSafe P) :=
  GeneralMemoryObstructionEquivalence.cSafe_greatest_memory_silent_domain
    (D.toGeneralMemoryObstructionEquivalence)

end

end MemorySupportDiscovery

/-!
  Summary:
  - `MemorySupportDiscovery` is a relation, not a predeclared map from memory
    atoms to semantic atoms.
  - Totality and uniqueness on both sides let Lean construct
    `MemoryAtom ≃ SemanticAtom`.
  - Support preservation and the discovered equivalence recover silence,
    nonempty-production, and greatest-domain structure.

  Remaining boundary:
  - The discovery relation is still a certificate.  A real runtime or a richer
    ontology theorem must provide it.
  - This does not prove the seven `SemanticAtom`s are complete; it proves that
    once an independent memory layer has exactly their support basis, the atom
    equivalence is discovered rather than assumed.
-/
