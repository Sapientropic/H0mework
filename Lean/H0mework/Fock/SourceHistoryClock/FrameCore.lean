import H0mework.Fock.SourceHistoryClock.Fock

/-! An actual native point and its next effect generate the entire existing clock model frame. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockFrame

open SourceClockModel

noncomputable section

def effect (depth : Nat) : Model := action (Fock.point depth) - Fock.point depth

theorem mass_effect (depth : Nat) : massRead (effect depth) = 0 := by
  rw [effect, map_sub, massRead_action, sub_self]

theorem clock_effect (depth : Nat) : clockRead (effect depth) = 1 := by
  rw [effect, map_sub, clockRead_action, add_sub_cancel_left, Fock.mass_current]

theorem action_effect (depth : Nat) : action (effect depth) = effect depth := by
  apply (model_ext_iff _ _).mpr
  constructor
  · exact massRead_action _
  · rw [clockRead_action, mass_effect, add_zero]

theorem reconstruction (depth : Nat) (value : Model) :
    value = massRead value • Fock.point depth +
      (clockRead value - massRead value * clockRead (Fock.point depth)) • effect depth := by
  apply (model_ext_iff _ _).mpr
  constructor
  · simp only [map_add, map_smul, Fock.mass_current, mass_effect, smul_eq_mul,
      mul_one, mul_zero, add_zero]
  · simp only [map_add, map_smul, clock_effect, smul_eq_mul, mul_one]
    ring

def coordinates (depth : Nat) : Model →ₗ[ℤ] ℤ × ℤ :=
  massRead.prod (clockRead - massRead.smulRight (clockRead (Fock.point depth)))

def rebuild (depth : Nat) : (ℤ × ℤ) →ₗ[ℤ] Model :=
  (LinearMap.fst ℤ ℤ ℤ).smulRight (Fock.point depth) +
    (LinearMap.snd ℤ ℤ ℤ).smulRight (effect depth)

theorem coordinates_apply (depth : Nat) (value : Model) :
    coordinates depth value =
      (massRead value, clockRead value - massRead value * clockRead (Fock.point depth)) := rfl

theorem rebuild_coordinates (depth : Nat) (value : Model) :
    rebuild depth (coordinates depth value) = value :=
  (reconstruction depth value).symm

theorem coordinates_rebuild (depth : Nat) (value : ℤ × ℤ) :
    coordinates depth (rebuild depth value) = value := by
  apply Prod.ext
  · change massRead (value.1 • Fock.point depth + value.2 • effect depth) = value.1
    simp only [map_add, map_smul, Fock.mass_current, mass_effect, smul_eq_mul,
      mul_one, mul_zero, add_zero]
  · change clockRead (value.1 • Fock.point depth + value.2 • effect depth) -
      massRead (value.1 • Fock.point depth + value.2 • effect depth) * clockRead (Fock.point depth) = value.2
    simp only [map_add, map_smul, Fock.mass_current, mass_effect, clock_effect, smul_eq_mul,
      mul_one, mul_zero, add_zero]
    ring

def frame (depth : Nat) : Model ≃ₗ[ℤ] ℤ × ℤ :=
  LinearEquiv.ofLinearMap (coordinates depth) (rebuild depth)
    (LinearMap.ext (coordinates_rebuild depth)) (LinearMap.ext (rebuild_coordinates depth))

theorem coordinates_point (depth : Nat) : coordinates depth (Fock.point depth) = (1, 0) := by
  rw [coordinates_apply, Fock.mass_current, one_mul, sub_self]

theorem coordinates_effect (depth : Nat) : coordinates depth (effect depth) = (0, 1) := by
  rw [coordinates_apply, mass_effect, clock_effect, zero_mul, sub_zero]

end
end SourceClockFrame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
