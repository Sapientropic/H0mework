import H0mework.Fock.HistoryConditional.NativeObserversUpdate
import H0mework.Fock.HistoryConditional.NativeKeysSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeKeys

abbrev State (bound : Nat) := SourceConditionalNativeObservers.State (ZMod 2) bound

def seed : State 0 := SourceConditionalNativeObservers.seed (fun index : Nat => (index : ZMod 2))

def advance (bound : Nat) (previous : State bound) : State (bound + 1) :=
  SourceConditionalNativeObservers.advance (fun index : Nat => (index : ZMod 2)) bound previous

def generate : (bound : Nat) → State bound :=
  SourceConditionalNativeObservers.generate (fun index : Nat => (index : ZMod 2))

theorem generated_next (bound : Nat) : generate (bound + 1) = advance bound (generate bound) := rfl

end SourceConditionalNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
