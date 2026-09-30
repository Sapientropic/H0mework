import H0mework.Fock.InverseDistribution.BirthNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionStream

abbrev State (Key : Type*) (bound : Nat) :=
  Key → Nat × (Fin (bound + 1) → Option (Nat × ℚ) × ℚ)

def weight (entry : Option (Nat × ℚ) × ℚ) : ℚ :=
  (entry.1.map Prod.snd).getD 0 + entry.2

def source {Key : Type*} (bound : Nat) (state : State Key bound) : SourceConditionalNativeObservers.State Key bound :=
  fun key => ((state key).1, fun actor => weight ((state key).2 actor))

def seed {Key : Type*} [DecidableEq Key] (read : Nat → Key) (program : Nat × Nat) : State Key 0 :=
  let initial := SourceConditionalNativeObservers.seed read
  fun key => ((initial key).1, SourceNativeInverseDistribution.split 0 program (initial key).2)

def step {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat)
    (previous : State Key bound) : State Key (bound + 1) :=
  let counts := SourceConditionalNativeObservers.advance read bound (source bound previous)
  let entries := SourceInverseDistributionBirth.advance read bound program
    (fun key => (previous key).1) (fun key => (previous key).2)
  fun key => ((counts key).1, entries key)

def generate {Key : Type*} [DecidableEq Key] (read : Nat → Key) (program : Nat × Nat) :
    (bound : Nat) → State Key bound :=
  Nat.rec (seed read program) (fun bound previous => step read bound program previous)

theorem generated_next {Key : Type*} [DecidableEq Key] (read : Nat → Key) (program : Nat × Nat) (bound : Nat) :
    generate read program (bound + 1) = step read bound program (generate read program bound) := rfl

end SourceInverseDistributionStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
