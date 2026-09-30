import H0mework.Fock.HistoryConditional.NativeInverseNative
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeProgramInverse

def decodeActor (bound : Nat) (program : Nat × Nat) (target : Nat) : Option (Fin (bound + 1)) :=
  match decode program target with
  | none => none
  | some state => if inside : 1 ≤ state ∧ state ≤ bound + 1 then
      some ⟨state - 1, by omega⟩
    else none

def row (bound : Nat) (program : Nat × Nat) (target : Nat) (actor : Fin (bound + 1)) : ℚ :=
  if decodeActor bound program target = some actor then 1 else 0

end SourceNativeProgramInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
