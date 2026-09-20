/-
  Proposition 34: reflexive λ obstruction produces memory under a certified
  adapter.

  Proposition 32 proves that canonical obstruction support and memory
  production are equivalent presentations.  Proposition 33 proves the
  unguarded/global λ no-go core for reflexive queries: a write that changes a
  later read observation rules out an unguarded λ certificate.

  This file connects those two sides without pretending the runtime adapter is
  automatic.  A `ReflexiveMemoryAdapter` is the mechanism-faithfulness witness:
  it says which memory epistemic type a concrete observation-changing read/write
  loop produces, and proves that this type is exactly the local memory
  production support.  Once that adapter exists, the λ no-go reason is the same
  support object as memory production and canonical reopen support.

  Boundary: the theorem is intentionally about the no-go reason
  `∃ x, read (write x) ≠ read x`, not about the bare proposition "no global
  certificate exists".  The latter has no useful converse in general: a
  certificate can fail to exist for reasons other than observation-changing
  reflexivity.
-/

import H0mework.Realization.Reflexive.StatefulRead

/-! ## Reflexive λ obstruction support -/

/-- Local reason why an unguarded reflexive λ cannot commute at a state:
    observing after the trace write differs from observing before it. -/
def ReflexiveLambdaObstruction {State Observation : Type*}
    (q : ReflexiveQuery State Observation) (x : State) : Prop :=
  q.read (q.write x) ≠ q.read x

/-- Global no-go reason for an unguarded reflexive λ: some state has a
    read-after-write / read-before-write observation mismatch. -/
def NoGlobalLambdaReason {State Observation : Type*}
    (q : ReflexiveQuery State Observation) : Prop :=
  exists x, ReflexiveLambdaObstruction q x

/-- A concrete runtime/read-write adapter from reflexive observation changes to
    canonical memory production.  The `memoryOf` function may classify different
    states into different epistemic memory types; the certificate says the
    chosen type is exactly the produced memory at that state. -/
structure ReflexiveMemoryAdapter {State Observation : Type*}
    (P : CSafePredicates State) (q : ReflexiveQuery State Observation) where
  memoryOf : State -> MemoryEpistemicType
  observation_iff_memory :
    forall x, ReflexiveLambdaObstruction q x <->
      MemoryProduction P x (memoryOf x)

namespace ReflexiveMemoryAdapter

variable {State Observation Obstruction : Type*}
variable {P : CSafePredicates State}
variable {q : ReflexiveQuery State Observation}

/-- THEOREM 1: under a certified adapter, local reflexive λ obstruction is
    exactly local memory production. -/
theorem obstruction_iff_memoryProduction
    (A : ReflexiveMemoryAdapter P q) (x : State) :
    ReflexiveLambdaObstruction q x <->
      MemoryProduction P x (A.memoryOf x) :=
  A.observation_iff_memory x

/-- THEOREM 2: the same local obstruction is exactly canonical reopen support
    for the reopen case corresponding to the produced memory type. -/
theorem obstruction_iff_canonicalSupport
    (A : ReflexiveMemoryAdapter P q) (x : State) :
    ReflexiveLambdaObstruction q x <->
      canonicalReopenSupport P x (memoryToReopen (A.memoryOf x)) := by
  exact (A.observation_iff_memory x).trans
    (memoryProduction_iff_canonicalSupport P x (A.memoryOf x))

/-- THEOREM 3: the global λ no-go reason is exactly existence of memory
    production at some state, through the adapter's memory classifier. -/
theorem noGlobalReason_iff_exists_memoryProduction
    (A : ReflexiveMemoryAdapter P q) :
    NoGlobalLambdaReason q <->
      exists x, MemoryProduction P x (A.memoryOf x) := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (A.observation_iff_memory x).mp hx⟩
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (A.observation_iff_memory x).mpr hx⟩

/-- THEOREM 4: the global λ no-go reason is also exactly existence of canonical
    reopen support for the memory-decoded reopen case. -/
theorem noGlobalReason_iff_exists_canonicalSupport
    (A : ReflexiveMemoryAdapter P q) :
    NoGlobalLambdaReason q <->
      exists x, canonicalReopenSupport P x (memoryToReopen (A.memoryOf x)) := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (A.obstruction_iff_canonicalSupport x).mp hx⟩
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨x, (A.obstruction_iff_canonicalSupport x).mpr hx⟩

/-- THEOREM 5: any produced memory witness gives the Proposition 33 no-go
    theorem for unguarded/global λ certificates. -/
theorem no_unguarded_lambda_of_memoryProduction
    (A : ReflexiveMemoryAdapter P q)
    (hmem : exists x, MemoryProduction P x (A.memoryOf x)) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  exact no_unguarded_lambda_of_observation_change q
    ((A.noGlobalReason_iff_exists_memoryProduction).mpr hmem)

/-- THEOREM 6: equivalently, canonical reopen support for the adapter-decoded
    case is enough to rule out an unguarded/global λ certificate. -/
theorem no_unguarded_lambda_of_canonicalSupport
    (A : ReflexiveMemoryAdapter P q)
    (hsupport :
      exists x, canonicalReopenSupport P x (memoryToReopen (A.memoryOf x))) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  exact no_unguarded_lambda_of_observation_change q
    ((A.noGlobalReason_iff_exists_canonicalSupport).mpr hsupport)

end ReflexiveMemoryAdapter

/-!
  Summary:
  - A reflexive observation mismatch is the local no-go reason for global λ.
  - Given a mechanism-faithfulness adapter, that local reason is precisely
    `MemoryProduction` and precisely canonical reopen support.
  - Therefore reflexivity that changes observations is not merely "a failed
    λ"; under the adapter it is a memory-producing obstruction.
-/
