import H0mework.Fock.SourceHistoryClock.BinomialRestriction

/-! The same source action generates the square evolution and its integer linear historical readout. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock

noncomputable section

theorem squareRead_action (value : Model) :
    squareRead (action value) = squareRead value + 2 * clockRead value - massRead value := by
  change 2 * secondRead (action value) - clockRead (action value) + massRead (action value) = _
  rw [secondRead_action, clockRead_action, massRead_action]
  change _ = (2 * secondRead value - clockRead value + massRead value) + 2 * clockRead value - massRead value
  ring

def pastSquare (steps : Nat) : Model →ₗ[ℤ] ℤ :=
  squareRead - (2 * (steps : ℤ)) • (clockRead - massRead) + ((steps : ℤ) ^ 2) • massRead

theorem pastSquare_point (steps first : Nat) :
    pastSquare steps (Fock.point (first + steps)) = (first : ℤ) ^ 2 := by
  change squareRead (Fock.point (first + steps)) -
    (2 * (steps : ℤ)) * (clockRead (Fock.point (first + steps)) - massRead (Fock.point (first + steps))) +
      (steps : ℤ) ^ 2 * massRead (Fock.point (first + steps)) = _
  rw [Fock.square_point, Fock.clock_point, Fock.mass_point, Nat.cast_add]
  ring

theorem effect_is_actual (depth : Nat) : Frame.effect depth = Fock.point (depth + 1) - Fock.point depth := by
  rw [Frame.effect, Fock.point_next]

theorem secondEffect_is_actual (depth : Nat) :
    Frame.secondEffect depth = Fock.point (depth + 2) - (2 : ℤ) • Fock.point (depth + 1) + Fock.point depth := by
  rw [Frame.secondEffect, effect_is_actual, map_sub, Fock.point_next, Fock.point_next, two_smul]
  abel

theorem square_secondEffect (depth : Nat) : squareRead (Frame.secondEffect depth) = 2 := by
  change 2 * secondRead (Frame.secondEffect depth) - clockRead (Frame.secondEffect depth) + massRead (Frame.secondEffect depth) = _
  rw [Frame.second_secondEffect, Frame.clock_secondEffect, Frame.mass_secondEffect]
  norm_num

end
end SourceBinomialClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
