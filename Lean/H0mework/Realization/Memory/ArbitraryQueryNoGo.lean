/-
  Proposition 45: canonical reflexive memory support.

  Propositions 34, 40, 41, and 44 deliberately keep a mechanism-faithfulness
  adapter in the path from reflexive observation changes to the seven-case
  `MemoryEpistemicType` ontology.  That boundary is real: an arbitrary
  `CSafePredicates P` can be completely safe while an unrelated reflexive query
  still changes its observation, so there is no unconditional theorem of the
  form

      ReflexiveLambdaObstruction q x <-> exists m, MemoryProduction P x m

  for arbitrary `P` and `q`.

  This file proves both sides of that line:

    * the arbitrary `P`/`q` equivalence is false, by a concrete counterexample;
    * the canonical support forced by reflexivity itself is a one-atom memory
      production object, and for that object reflexivity iff memory is a theorem
      with no adapter/equivalence certificate.

  Boundary: this is the foundational reflexivity-memory isomorphism for the
  reflexive query algebra itself.  Mapping that one forced atom into the richer
  seven-case AIppocampus memory ontology still requires a runtime classifier,
  because choosing which epistemic family a concrete trace write belongs to is
  mechanism-specific.
-/

import H0mework.Realization.Memory.IndependentAdapter

/-! ## Why arbitrary `P`/`q` cannot have an unconditional memory equivalence -/

/-- The all-safe predicate family.  It is intentionally unrelated to any
reflexive query: every lower semantic obligation holds at every state. -/
def allSafePredicates (State : Type*) : CSafePredicates State where
  sourceBacked := fun _ => True
  authoritySafe := fun _ => True
  graphConfluent := fun _ => True
  gaugeNonleaking := fun _ => True
  contractionSafe := fun _ => True
  omegaConsistent := fun _ => True
  freshnessSafe := fun _ => True

/-- In the all-safe predicate family, canonical seven-case memory production is
empty everywhere. -/
theorem allSafe_memoryProduction_false {State : Type*}
    (x : State) (m : MemoryEpistemicType) :
    ¬ MemoryProduction (allSafePredicates State) x m := by
  intro hm
  cases m <;>
    simp [MemoryProduction, AtomFailure, semanticObligationSemantics,
      semanticHolds, allSafePredicates, memoryToSemanticAtom] at hm

/-- THEOREM 1: there is no unconditional equivalence between reflexive
observation change and seven-case canonical memory production for arbitrary
`P` and `q`.  The counterexample is simple: `P` is all-safe while the
reflexive counter query changes its observation at `0`. -/
theorem no_unconditional_reflexive_memory_equiv_for_arbitrary_P :
    ¬ (∀ x : Nat,
      ReflexiveLambdaObstruction ReflexiveQuery.natCounter x <->
        ∃ m, MemoryProduction (allSafePredicates Nat) x m) := by
  intro h
  have hobs : ReflexiveLambdaObstruction ReflexiveQuery.natCounter 0 := by
    norm_num [ReflexiveLambdaObstruction, ReflexiveQuery.natCounter]
  rcases (h 0).mp hobs with ⟨m, hm⟩
  exact allSafe_memoryProduction_false 0 m hm

/-! ## Canonical one-atom reflexive memory support -/

/-- The primitive memory atom forced by reflexivity itself: the trace write
changed the next read observation. -/
inductive ReflexiveMemoryAtom where
  | observationChanged
  deriving DecidableEq, Repr

/-- Canonical reflexive memory production.  There is exactly one atom, and it
is produced exactly when read-after-write differs from read-before-write. -/
def ReflexiveMemoryProduction {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    ReflexiveMemoryAtom -> Prop
  | ReflexiveMemoryAtom.observationChanged => ReflexiveLambdaObstruction q x

/-- A state is silent for the canonical reflexive memory support when no
reflexive memory atom is produced there. -/
def ReflexiveMemorySilentAt {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : Prop :=
  forall a, ReflexiveMemoryProduction q x a -> False

/-- THEOREM 2: local reflexive λ obstruction is exactly canonical reflexive
memory production.  This is the non-adapter, foundational support isomorphism:
the memory atom is not chosen by a classifier; it is forced by the read/write
algebra. -/
theorem reflexiveObstruction_iff_reflexiveMemoryProduction
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    ReflexiveLambdaObstruction q x <->
      ReflexiveMemoryProduction q x ReflexiveMemoryAtom.observationChanged := by
  rfl

/-- THEOREM 3: reflexive memory silence is exactly absence of local reflexive
λ obstruction. -/
theorem reflexiveMemorySilent_iff_no_obstruction
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) :
    ReflexiveMemorySilentAt q x <-> ¬ ReflexiveLambdaObstruction q x := by
  constructor
  · intro hsilent hobstruction
    exact hsilent ReflexiveMemoryAtom.observationChanged hobstruction
  · intro hno atom hprod
    cases atom
    exact hno hprod

/-- THEOREM 4: global reflexive λ no-go reason is exactly existence of the
canonical reflexive memory atom. -/
theorem noGlobalReason_iff_exists_reflexiveMemoryProduction
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    NoGlobalLambdaReason q <->
      ∃ x, ReflexiveMemoryProduction q x ReflexiveMemoryAtom.observationChanged := by
  rfl

/-- THEOREM 5: equivalently, global reflexive λ no-go is nonempty canonical
reflexive memory support. -/
theorem noGlobalReason_iff_reflexiveMemorySupport_nonempty
    {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    NoGlobalLambdaReason q <->
      ∃ x a, ReflexiveMemoryProduction q x a := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, ReflexiveMemoryAtom.observationChanged, hx⟩
  · rintro ⟨x, atom, hprod⟩
    cases atom
    exact ⟨x, hprod⟩

/-- THEOREM 6: canonical reflexive memory production is exactly the Proposition
33 obstruction that rules out an unguarded/global λ certificate. -/
theorem no_unguarded_lambda_of_reflexiveMemoryProduction
    {State Observation Obstruction : Type*}
    (q : ReflexiveQuery State Observation)
    (hmem :
      ∃ x, ReflexiveMemoryProduction q x ReflexiveMemoryAtom.observationChanged) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  exact no_unguarded_lambda_of_observation_change q hmem

/-! ## Presentation uniqueness for reflexive memory -/

/-- A representation of canonical reflexive memory support.  A representation
is canonical only when it decodes soundly and completely to the forced
one-atom support above. -/
structure ReflexiveMemoryPresentation {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (O : Type*) where
  classify : State -> O
  decodes : O -> ReflexiveMemoryAtom -> Prop
  sound :
    forall x atom, decodes (classify x) atom ->
      ReflexiveMemoryProduction q x atom
  complete :
    forall x atom, ReflexiveMemoryProduction q x atom ->
      decodes (classify x) atom

/-- THEOREM 7: any sound-and-complete reflexive memory presentation decodes to
exactly the canonical reflexive memory support. -/
theorem reflexiveMemoryPresentation_unique_support
    {State Observation O : Type*}
    (q : ReflexiveQuery State Observation)
    (pres : ReflexiveMemoryPresentation q O)
    (x : State) (atom : ReflexiveMemoryAtom) :
    pres.decodes (pres.classify x) atom <->
      ReflexiveMemoryProduction q x atom := by
  constructor
  · exact pres.sound x atom
  · exact pres.complete x atom

/-- THEOREM 8: any two sound-and-complete reflexive memory presentations are
equivalent after decoding; representation choices add no canonical content. -/
theorem reflexiveMemoryPresentations_equivalent
    {State Observation O₁ O₂ : Type*}
    (q : ReflexiveQuery State Observation)
    (pres₁ : ReflexiveMemoryPresentation q O₁)
    (pres₂ : ReflexiveMemoryPresentation q O₂)
    (x : State) (atom : ReflexiveMemoryAtom) :
    pres₁.decodes (pres₁.classify x) atom <->
      pres₂.decodes (pres₂.classify x) atom := by
  calc
    pres₁.decodes (pres₁.classify x) atom <->
        ReflexiveMemoryProduction q x atom :=
      reflexiveMemoryPresentation_unique_support q pres₁ x atom
    _ <-> pres₂.decodes (pres₂.classify x) atom :=
      (reflexiveMemoryPresentation_unique_support q pres₂ x atom).symm

/-- The canonical presentation represents a state by its full reflexive memory
support predicate. -/
def canonicalReflexiveMemoryPresentation {State Observation : Type*}
    (q : ReflexiveQuery State Observation) :
    ReflexiveMemoryPresentation q (ReflexiveMemoryAtom -> Prop) where
  classify := fun x => ReflexiveMemoryProduction q x
  decodes := fun support atom => support atom
  sound := by
    intro _x _atom h
    exact h
  complete := by
    intro _x _atom h
    exact h

/-!
  Summary:
  - `no_unconditional_reflexive_memory_equiv_for_arbitrary_P` marks the false
    overclaim: arbitrary seven-case memory production cannot be identified with
    unrelated reflexive observation changes.
  - `reflexiveObstruction_iff_reflexiveMemoryProduction` is the foundational
    reflexivity-memory isomorphism for the canonical support object forced by
    the reflexive query algebra itself.
  - Seven-case AIppocampus memory classification remains a runtime
    mechanism-faithfulness obligation; the canonical one-atom support is what
    any such classifier must preserve.
-/
