import H0mework.Fock.HistoryConditional.CopyKeysNative
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

def selector (index : Nat) : Nat := ((2 * (index + 3)).factorial + 1).minFac

def width (bound : Nat) : Nat := selector (bound + 1) / 2 - (bound + 1) - 2 + bound + 1

def read (bound state : Nat) : List (Finset Nat.Primes) :=
  List.ofFn (fun time : Fin (width bound + 1) => SourceCopyNativeKeys.key (state + 1 + time.val))

end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
