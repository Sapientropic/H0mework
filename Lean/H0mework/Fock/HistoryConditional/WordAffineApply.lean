import H0mework.Fock.HistoryConditional.WordAffineNative
import H0mework.Fock.HistoryConditional.CopyHistoryDecode

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyWordAffine

def applyRecovered (bound : Nat) (program : Nat × Nat) (row : Fin (bound + 1) → ℚ) : Option Nat :=
  (SourceCopyNativeHistory.decodeRow bound row).map (fun actor => execute program (actor.val + 1))

end SourceCopyWordAffine
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
