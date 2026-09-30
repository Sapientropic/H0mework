import H0mework.Fock.InverseDistribution.Native
import H0mework.Fock.HistoryConditional.NativeObserversUpdate

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionBirth

def scaleEntry (scale : ℚ) (entry : Option (Nat × ℚ) × ℚ) : Option (Nat × ℚ) × ℚ :=
  (entry.1.map (fun pair => (pair.1, scale * pair.2)), scale * entry.2)

def advance {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat)
    (counts : Key → Nat) (previous : Key → Fin (bound + 1) → Option (Nat × ℚ) × ℚ) :
    Key → Fin (bound + 2) → Option (Nat × ℚ) × ℚ := fun key =>
  if key = read (bound + 1) then
    Fin.lastCases (SourceNativeInverseDistribution.splitEntry program (bound + 2) ((counts key + 1 : Nat) : ℚ)⁻¹)
      (fun actor => scaleEntry ((counts key : ℚ) / (counts key + 1 : Nat)) (previous key actor))
  else Fin.lastCases (SourceNativeInverseDistribution.splitEntry program (bound + 2) 0) (previous key)

end SourceInverseDistributionBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
