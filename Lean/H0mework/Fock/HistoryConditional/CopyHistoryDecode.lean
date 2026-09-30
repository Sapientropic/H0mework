import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeHistory

def decodeRow (bound : Nat) (row : Fin (bound + 1) → ℚ) : Option (Fin (bound + 1)) :=
  (List.finRange (bound + 1)).find? (fun actor => row actor != 0)

end SourceCopyNativeHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
