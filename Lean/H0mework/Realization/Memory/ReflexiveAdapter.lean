/-
  Proposition 41: reflexive λ no-go through independent memory production.

  Proposition 34 connects reflexive read-after-write observation changes to the
  canonical `MemoryProduction` presentation.  Proposition 40 introduces an
  independently specified memory-production contract.

  This file composes those ideas without erasing the boundary: a concrete
  reflexive query needs an adapter that identifies which independently
  specified memory production its observation-changing write produces.  Once
  that adapter exists, the unguarded/global λ no-go reason is exactly the
  existence of independent memory production along the adapter-selected memory
  type.
-/

import H0mework.Realization.Memory.ReflexiveSupport
import H0mework.Realization.Memory.IndependentProduction

/-! ## Independent reflexive memory adapter -/

/-- A runtime/read-write adapter from reflexive observation changes to an
independent memory-production contract. -/
structure ReflexiveIndependentMemoryAdapter {State Observation : Type*}
    (M : MemoryProductionContract State MemoryEpistemicType)
    (q : ReflexiveQuery State Observation) where
  memoryOf : State -> MemoryEpistemicType
  observation_iff_produces :
    forall x, ReflexiveLambdaObstruction q x <->
      M.produces x (memoryOf x)

namespace ReflexiveIndependentMemoryAdapter

variable {State Observation Obstruction : Type*}
variable {M : MemoryProductionContract State MemoryEpistemicType}
variable {q : ReflexiveQuery State Observation}

/-- THEOREM 1: local reflexive λ obstruction is exactly independent memory
production for the adapter-selected memory type. -/
theorem obstruction_iff_independentProduction
    (A : ReflexiveIndependentMemoryAdapter M q) (x : State) :
    ReflexiveLambdaObstruction q x <->
      M.produces x (A.memoryOf x) :=
  A.observation_iff_produces x

/-- THEOREM 2: the global λ no-go reason is exactly existence of independent
memory production along the adapter classifier. -/
theorem noGlobalReason_iff_exists_independentProduction
    (A : ReflexiveIndependentMemoryAdapter M q) :
    NoGlobalLambdaReason q <->
      exists x, M.produces x (A.memoryOf x) := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (A.observation_iff_produces x).mp hx⟩
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (A.observation_iff_produces x).mpr hx⟩

/-- THEOREM 3: independent memory production rules out an unguarded/global λ
certificate for the reflexive query. -/
theorem no_unguarded_lambda_of_independentProduction
    (A : ReflexiveIndependentMemoryAdapter M q)
    (hmem : exists x, M.produces x (A.memoryOf x)) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  exact no_unguarded_lambda_of_observation_change q
    ((A.noGlobalReason_iff_exists_independentProduction).mpr hmem)

end ReflexiveIndependentMemoryAdapter

/-! ## From canonical adapters to independent adapters -/

/-- If an independent memory layer is equivalent to the canonical obstruction
layer, any canonical reflexive adapter induces an independent reflexive adapter. -/
def ReflexiveMemoryAdapter.toIndependent {State Observation : Type*}
    {P : CSafePredicates State}
    {M : MemoryProductionContract State MemoryEpistemicType}
    {q : ReflexiveQuery State Observation}
    (E : MemoryObstructionEquivalence P M)
    (A : ReflexiveMemoryAdapter P q) :
    ReflexiveIndependentMemoryAdapter M q where
  memoryOf := A.memoryOf
  observation_iff_produces := by
    intro x
    exact (A.observation_iff_memory x).trans
      ((independentProduces_iff_canonicalMemoryProduction E x (A.memoryOf x)).symm)

/-- THEOREM 4: through a memory-obstruction equivalence, canonical adapter
memory support and independent memory support are the same support. -/
theorem canonicalAdapter_independentSupport_iff {State Observation : Type*}
    {P : CSafePredicates State}
    {M : MemoryProductionContract State MemoryEpistemicType}
    {q : ReflexiveQuery State Observation}
    (E : MemoryObstructionEquivalence P M)
    (A : ReflexiveMemoryAdapter P q) (x : State) :
    M.produces x (A.memoryOf x) <->
      MemoryProduction P x (A.memoryOf x) := by
  exact independentProduces_iff_canonicalMemoryProduction E x (A.memoryOf x)

/-!
  Boundary:
  - The theorem is still adapter-relative.  It proves the algebraic consequence
    once the runtime says which memory type a reflexive observation change
    produces.
  - It does not claim that every absence of an unguarded λ certificate is caused
    by reflexive memory; Proposition 34's no-go boundary still applies.
-/
