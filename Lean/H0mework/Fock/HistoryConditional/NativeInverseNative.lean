import H0mework.Fock.HistoryConditional.WordAffineNative

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

def decode (program : Nat × Nat) (target : Nat) : Option Nat :=
  if 0 < program.1 ∧ program.2 < target + 1 ∧ program.1 ∣ target + 1 - program.2 then
    some ((target + 1 - program.2) / program.1 - 1)
  else none

end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
