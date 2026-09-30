import H0mework.Fock.HistoryConditional.NativeInverseNative
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeInverseDistribution

def splitEntry (program : Nat × Nat) (target : Nat) (weight : ℚ) : Option (Nat × ℚ) × ℚ :=
  match SourceNativeProgramInverse.decode program target with
  | none => (none, weight)
  | some state => (some (state, weight), 0)

def split (bound : Nat) (program : Nat × Nat) (weights : Fin (bound + 1) → ℚ) :
    Fin (bound + 1) → Option (Nat × ℚ) × ℚ :=
  fun actor => splitEntry program (actor.val + 1) (weights actor)

end SourceNativeInverseDistribution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
