/-
  Proposition 44: canonical reflexive no-go without an external equivalence
  certificate.

  Proposition 41 showed how a canonical `ReflexiveMemoryAdapter` induces an
  independent reflexive adapter once a `MemoryObstructionEquivalence` is
  supplied.  Proposition 43 constructs that equivalence for the canonical
  memory-production contract.

  This file composes them into the direct canonical statement: a mechanism
  faithfulness witness for reflexive observation-changing reads is enough to
  produce the independent-memory λ no-go bridge, without passing an additional
  equivalence certificate.
-/

import H0mework.Realization.Memory.ReflexiveAdapter
import H0mework.Realization.Memory.ProductionContract

/-! ## Canonical reflexive independent adapter -/

namespace ReflexiveMemoryAdapter

variable {State Observation Obstruction : Type*}
variable {P : CSafePredicates State}
variable {q : ReflexiveQuery State Observation}

/-- A canonical reflexive-memory adapter induces an independent-memory adapter
for the canonical memory-production contract.  The equivalence certificate is
the constructed one from Proposition 43, not an external input. -/
noncomputable def toCanonicalIndependent
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q) :
    ReflexiveIndependentMemoryAdapter
      (canonicalMemoryProductionContract P hind) q :=
  A.toIndependent
    (CanonicalMemoryProductionContract.memoryObstructionEquivalence P hind)

/-- THEOREM 1: the induced canonical independent adapter keeps the same memory
classifier as the canonical adapter. -/
theorem toCanonicalIndependent_memoryOf
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q) (x : State) :
    (A.toCanonicalIndependent hind).memoryOf x = A.memoryOf x := by
  rfl

/-- THEOREM 2: local reflexive λ obstruction is exactly independent production
in the canonical memory-production contract. -/
theorem obstruction_iff_canonicalIndependentProduction
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q) (x : State) :
    ReflexiveLambdaObstruction q x <->
      (canonicalMemoryProductionContract P hind).produces x (A.memoryOf x) := by
  exact (A.toCanonicalIndependent hind).observation_iff_produces x

/-- THEOREM 3: canonical independent production support is the same support as
canonical `MemoryProduction`. -/
theorem canonicalIndependentProduction_iff_memoryProduction
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q) (x : State) :
    (canonicalMemoryProductionContract P hind).produces x (A.memoryOf x) <->
      MemoryProduction P x (A.memoryOf x) := by
  rfl

/-- THEOREM 4: the global λ no-go reason is exactly existence of canonical
independent memory production along the adapter classifier. -/
theorem noGlobalReason_iff_exists_canonicalIndependentProduction
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q) :
    NoGlobalLambdaReason q <->
      exists x,
        (canonicalMemoryProductionContract P hind).produces x (A.memoryOf x) := by
  exact (A.toCanonicalIndependent hind).noGlobalReason_iff_exists_independentProduction

/-- THEOREM 5: canonical independent memory production rules out an
unguarded/global λ certificate. -/
theorem no_unguarded_lambda_of_canonicalIndependentProduction
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q)
    (hmem :
      exists x,
        (canonicalMemoryProductionContract P hind).produces x (A.memoryOf x)) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  exact (A.toCanonicalIndependent hind).no_unguarded_lambda_of_independentProduction
    hmem

/-- THEOREM 6: equivalently, the canonical adapter's memory-production support
gives the independent-memory no-go theorem through the constructed canonical
contract. -/
theorem no_unguarded_lambda_of_canonicalMemoryProduction_via_independent
    (hind : AtomIndependent (semanticObligationSemantics P))
    (A : ReflexiveMemoryAdapter P q)
    (hmem : exists x, MemoryProduction P x (A.memoryOf x)) :
    UnguardedLambdaCertificate State Observation Obstruction q -> False := by
  apply no_unguarded_lambda_of_canonicalIndependentProduction
    (P := P) (q := q) hind A
  rcases hmem with ⟨x, hx⟩
  exact ⟨x, hx⟩

end ReflexiveMemoryAdapter

/-!
  Boundary:
  - This removes the equivalence-certificate argument from the canonical
    reflexive path.
  - It still needs the concrete runtime to provide the `ReflexiveMemoryAdapter`
    itself, and it still needs lower atom independence for the canonical
    independent contract.
-/
