import H0mework.Fock.SourceHistoryClock.BinomialFock

/-! A source point and its two actual successive differences expose unit triangular moment directions. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Frame

noncomputable section

def effect (depth : Nat) : Model := action (Fock.point depth) - Fock.point depth
def secondEffect (depth : Nat) : Model := action (effect depth) - effect depth

theorem mass_effect (depth : Nat) : massRead (effect depth) = 0 := by
  rw [effect, map_sub, massRead_action, sub_self]

theorem clock_effect (depth : Nat) : clockRead (effect depth) = 1 := by
  rw [effect, map_sub, clockRead_action, add_sub_cancel_left, Fock.mass_point]

theorem second_effect (depth : Nat) : secondRead (effect depth) = clockRead (Fock.point depth) := by
  rw [effect, map_sub, secondRead_action, add_sub_cancel_left]

theorem mass_secondEffect (depth : Nat) : massRead (secondEffect depth) = 0 := by
  rw [secondEffect, map_sub, massRead_action, sub_self]

theorem clock_secondEffect (depth : Nat) : clockRead (secondEffect depth) = 0 := by
  rw [secondEffect, map_sub, clockRead_action, add_sub_cancel_left, mass_effect]

theorem second_secondEffect (depth : Nat) : secondRead (secondEffect depth) = 1 := by
  rw [secondEffect, map_sub, secondRead_action, add_sub_cancel_left, clock_effect]

theorem action_secondEffect (depth : Nat) : action (secondEffect depth) = secondEffect depth := by
  apply (model_ext_iff _ _).mpr
  refine ⟨massRead_action _, ?_, ?_⟩
  · rw [clockRead_action, mass_secondEffect, add_zero]
  · rw [secondRead_action, clock_secondEffect, add_zero]

theorem reconstruction (depth : Nat) (value : Model) :
    value = massRead value • Fock.point depth +
      (clockRead value - massRead value * clockRead (Fock.point depth)) • effect depth +
        (secondRead value - massRead value * secondRead (Fock.point depth) -
          (clockRead value - massRead value * clockRead (Fock.point depth)) * clockRead (Fock.point depth)) • secondEffect depth := by
  apply (model_ext_iff _ _).mpr
  constructor
  · simp only [map_add, map_smul, Fock.mass_point, mass_effect, mass_secondEffect,
      smul_eq_mul, mul_one, mul_zero, add_zero]
  constructor
  · simp only [map_add, map_smul, clock_effect, clock_secondEffect,
      smul_eq_mul, mul_one, mul_zero, add_zero]
    ring
  · simp only [map_add, map_smul, second_effect, second_secondEffect, smul_eq_mul, mul_one]
    ring

end
end SourceBinomialClock.Frame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
