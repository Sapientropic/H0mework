/-
  Proposition 46: the canonical reflexive memory contract.

  Proposition 45 proves the pointwise support isomorphism forced by reflexive
  query algebra:

      read-after-write changes observation  <->  the canonical reflexive
      memory atom is produced.

  This file lifts that support object into the same contract/maximality shape
  used for memory production elsewhere:

    * one-atom independence is characterized exactly as "there exists a
      changing state and there exists a silent state";
    * under that explicit independence certificate, the canonical reflexive
      memory support is a `MemoryProductionContract`;
    * non-silence of that contract is exactly the local reflexive λ
      obstruction, and global nonempty production is exactly the global
      λ no-go reason;
    * the silent states form the greatest domain with no reflexive memory
      production.

  This is still not the seven-case AIppocampus ontology.  It is the
  adapter-free contract that the richer ontology must refine or classify.
-/

import H0mework.Realization.Memory.ArbitraryQueryNoGo

/-! ## Independence for the one-atom reflexive support -/

/-- Independence for the canonical one-atom reflexive memory support.  This is
the memory-side analogue of `AtomIndependent`, stated directly for the support
from Proposition 45. -/
def ReflexiveMemoryAtomIndependent {State Observation : Type*}
    (q : ReflexiveQuery State Observation) : Prop :=
  forall assignment : ReflexiveMemoryAtom -> Prop,
    exists x, forall atom,
      ReflexiveMemoryProduction q x atom <-> assignment atom

/-- THEOREM 1: for a one-atom reflexive memory support, independence is exactly
the existence of both a changing state and a silent state.  This keeps the
`independent` field honest: it is not automatic, and it is not a hidden
taxonomy assumption. -/
theorem reflexiveMemoryAtomIndependent_iff_change_and_silence
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    ReflexiveMemoryAtomIndependent q <->
      NoGlobalLambdaReason q /\ exists x, ReflexiveMemorySilentAt q x := by
  constructor
  · intro hind
    constructor
    · let assignment : ReflexiveMemoryAtom -> Prop := fun _ => True
      rcases hind assignment with ⟨x, hx⟩
      exact ⟨x, (hx ReflexiveMemoryAtom.observationChanged).mpr trivial⟩
    · let assignment : ReflexiveMemoryAtom -> Prop := fun _ => False
      rcases hind assignment with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      intro atom hprod
      exact (hx atom).mp hprod
  · rintro ⟨⟨xChange, hChange⟩, ⟨xSilent, hSilent⟩⟩ assignment
    by_cases hassign : assignment ReflexiveMemoryAtom.observationChanged
    · refine ⟨xChange, ?_⟩
      intro atom
      cases atom
      constructor
      · intro _h
        exact hassign
      · intro _h
        exact hChange
    · refine ⟨xSilent, ?_⟩
      intro atom
      cases atom
      constructor
      · intro hprod
        exact False.elim (hSilent ReflexiveMemoryAtom.observationChanged hprod)
      · intro h
        exact False.elim (hassign h)

/-! ## Canonical reflexive memory contract -/

/-- The canonical memory-production contract induced by a reflexive query.  The
only nontrivial input is the explicit one-atom independence certificate. -/
def canonicalReflexiveMemoryContract {State Observation : Type*}
    (q : ReflexiveQuery State Observation)
    (hind : ReflexiveMemoryAtomIndependent q) :
    MemoryProductionContract State ReflexiveMemoryAtom where
  produces := ReflexiveMemoryProduction q
  memorySilent := ReflexiveMemorySilentAt q
  product_shape := by
    intro x
    rfl
  independent := hind

namespace CanonicalReflexiveMemoryContract

variable {State Observation Obstruction : Type*}
variable (q : ReflexiveQuery State Observation)
variable (hind : ReflexiveMemoryAtomIndependent q)

/-- THEOREM 2: the canonical contract's production predicate is exactly
canonical reflexive memory production. -/
theorem produces_iff_reflexiveMemoryProduction
    (x : State) (atom : ReflexiveMemoryAtom) :
    (canonicalReflexiveMemoryContract q hind).produces x atom <->
      ReflexiveMemoryProduction q x atom := by
  rfl

/-- THEOREM 3: the canonical contract's silence predicate is exactly canonical
reflexive memory silence. -/
theorem silent_iff_reflexiveMemorySilent
    (x : State) :
    (canonicalReflexiveMemoryContract q hind).memorySilent x <->
      ReflexiveMemorySilentAt q x := by
  rfl

/-- THEOREM 4: local nonempty production in the canonical reflexive contract is
exactly local reflexive λ obstruction. -/
theorem local_nonempty_iff_reflexiveObstruction
    (x : State) :
    (exists atom, (canonicalReflexiveMemoryContract q hind).produces x atom) <->
      ReflexiveLambdaObstruction q x := by
  constructor
  · rintro ⟨atom, hprod⟩
    cases atom
    exact hprod
  · intro hobs
    exact ⟨ReflexiveMemoryAtom.observationChanged, hobs⟩

/-- THEOREM 5: global nonempty production in the canonical reflexive contract is
exactly the global reflexive λ no-go reason. -/
theorem global_nonempty_iff_noGlobalReason :
    (exists x atom, (canonicalReflexiveMemoryContract q hind).produces x atom) <->
      NoGlobalLambdaReason q := by
  constructor
  · rintro ⟨x, atom, hprod⟩
    cases atom
    exact ⟨x, hprod⟩
  · rintro ⟨x, hobs⟩
    exact ⟨x, ReflexiveMemoryAtom.observationChanged, hobs⟩

/-- THEOREM 6: canonical reflexive memory production gives exactly the
Proposition 33 no-go theorem for unguarded/global λ certificates. -/
theorem no_unguarded_lambda_of_global_nonempty
    (hprod :
      exists x atom, (canonicalReflexiveMemoryContract q hind).produces x atom) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  exact no_unguarded_lambda_of_observation_change q
    ((global_nonempty_iff_noGlobalReason q hind).mp hprod)

end CanonicalReflexiveMemoryContract

/-! ## Maximality: silent states as the greatest no-production domain -/

/-- A domain is reflexive-memory silent when every point in it produces no
canonical reflexive memory. -/
def ReflexiveMemorySilentDomain {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (D : State -> Prop) : Prop :=
  forall x, D x -> ReflexiveMemorySilentAt q x

/-- Greatest domain with no canonical reflexive memory production. -/
def IsGreatestReflexiveMemorySilentDomain {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (C : State -> Prop) : Prop :=
  ReflexiveMemorySilentDomain q C /\
    forall D : State -> Prop, ReflexiveMemorySilentDomain q D -> PredSubset D C

/-- THEOREM 7: the predicate of silent states is itself a silent domain. -/
theorem reflexiveSilentStates_silentDomain {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    ReflexiveMemorySilentDomain q (ReflexiveMemorySilentAt q) := by
  intro x hx
  exact hx

/-- THEOREM 8: every reflexive-memory silent domain is included in the silent
states. -/
theorem reflexiveSilentDomain_subset_silentStates {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (D : State -> Prop)
    (hD : ReflexiveMemorySilentDomain q D) :
    PredSubset D (ReflexiveMemorySilentAt q) := by
  intro x hx
  exact hD x hx

/-- THEOREM 9: the silent states are the greatest domain that produces no
canonical reflexive memory. -/
theorem reflexiveSilentStates_greatest {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    IsGreatestReflexiveMemorySilentDomain q (ReflexiveMemorySilentAt q) := by
  constructor
  · exact reflexiveSilentStates_silentDomain q
  · intro D hD
    exact reflexiveSilentDomain_subset_silentStates q D hD

/-!
  Summary:
  - P45 gives the forced support object: reflexive observation change iff the
    canonical reflexive memory atom is produced.
  - P46 packages that support object as a memory-production contract whenever
    the one-atom independence certificate is supplied, and proves the global
    nonempty-production iff global λ no-go correspondence.
  - The exact independence obligation is now characterized: it is equivalent to
    having both a changing state and a silent state.
-/
