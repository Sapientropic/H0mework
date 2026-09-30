import H0mework.Fock.HistoryConditional.WordAffineApply

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeWord

def runRecovered (bound : Nat) (word : List (Option Nat)) : (Fin (bound + 1) → ℚ) → Option Nat :=
  let program := SourceCopyWordAffine.compile word
  SourceCopyWordAffine.applyRecovered bound program

end SourceCopyNativeWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
