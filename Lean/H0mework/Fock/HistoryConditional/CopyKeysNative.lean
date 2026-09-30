import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeKeys

def seed : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, by decide⟩}

def advance (state : Nat) (previous : Finset Nat.Primes) : Finset Nat.Primes :=
  if prime : Nat.Prime (2 * state + 5) then insert ⟨2 * state + 5, prime⟩ previous else previous

def key : Nat → Finset Nat.Primes := Nat.rec seed (fun state previous => advance state previous)

theorem key_next (state : Nat) : key (state + 1) = advance state (key state) := rfl

def jointKey (materialIndex state : Nat) : Finset Nat.Primes × Finset Nat.Primes :=
  (key state, key ((state + 1) * (materialIndex + 1) - 1))

end SourceCopyNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
