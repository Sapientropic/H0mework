import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeObservers

abbrev State (Key : Type*) (bound : Nat) := Key → Nat × (Fin (bound + 1) → ℚ)

def seed {Key : Type*} [DecidableEq Key] (read : Nat → Key) : State Key 0 :=
  fun key => if key = read 0 then (1, fun _ => 1) else (0, fun _ => 0)

def advance {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat)
    (previous : State Key bound) : State Key (bound + 1) := fun key =>
  let old := previous key
  if key = read (bound + 1) then
    (old.1 + 1, Fin.lastCases ((old.1 + 1 : Nat) : ℚ)⁻¹
      (fun index => ((old.1 : ℚ) / (old.1 + 1 : Nat)) * old.2 index))
  else (old.1, Fin.lastCases 0 old.2)

def generate {Key : Type*} [DecidableEq Key] (read : Nat → Key) : (bound : Nat) → State Key bound :=
  Nat.rec (seed read) (fun bound previous => advance read bound previous)

theorem generated_next {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) :
    generate read (bound + 1) = advance read bound (generate read bound) := rfl

end SourceConditionalNativeObservers
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
