import H0mework.Fock.SourceHistoryClock.FrameCore

/-! The generated source frame gives the whole model action and its explicit inverse. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockFrame

open SourceClockModel

noncomputable section

theorem action_formula (depth : Nat) (value : Model) :
    action value = value + massRead value • effect depth := by
  apply (model_ext_iff _ _).mpr
  constructor
  · simp only [massRead_action, map_add, map_smul, mass_effect, smul_zero, add_zero]
  · simp only [clockRead_action, map_add, map_smul, clock_effect, smul_eq_mul, mul_one]

def inverse (depth : Nat) : Model →ₗ[ℤ] Model :=
  LinearMap.id - massRead.smulRight (effect depth)

theorem inverse_apply (depth : Nat) (value : Model) :
    inverse depth value = value - massRead value • effect depth := rfl

theorem inverse_action (depth : Nat) (value : Model) : inverse depth (action value) = value := by
  rw [inverse_apply, massRead_action, action_formula depth]
  abel

theorem action_inverse (depth : Nat) (value : Model) : action (inverse depth value) = value := by
  rw [action_formula depth, inverse_apply, map_sub, map_smul, mass_effect, smul_zero, sub_zero]
  abel

def actionEquiv (depth : Nat) : Model ≃ₗ[ℤ] Model :=
  LinearEquiv.ofLinearMap action (inverse depth)
    (LinearMap.ext (action_inverse depth)) (LinearMap.ext (inverse_action depth))

end
end SourceClockFrame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
