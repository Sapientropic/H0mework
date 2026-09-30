import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeWord

def step : Option Nat → Nat → Nat
  | none, state => state + 1
  | some materialIndex, state => (state + 1) * (materialIndex + 1) - 1

def run (word : List (Option Nat)) (state : Nat) : Nat := word.foldl (fun current letter => step letter current) state

end SourceCopyNativeWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
