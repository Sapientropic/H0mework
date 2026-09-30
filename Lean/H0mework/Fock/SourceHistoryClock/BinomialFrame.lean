import H0mework.Fock.SourceHistoryClock.BinomialEffects

/-! The generated unit triangular directions form an integer frame, with both inverses proved from the source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceBinomialClock.Frame

noncomputable section

private def firstCoefficient (depth : Nat) : Model →ₗ[ℤ] ℤ :=
  clockRead - massRead.smulRight (clockRead (Fock.point depth))

private def lastCoefficient (depth : Nat) : Model →ₗ[ℤ] ℤ :=
  secondRead - massRead.smulRight (secondRead (Fock.point depth)) -
    (firstCoefficient depth).smulRight (clockRead (Fock.point depth))

def coordinates (depth : Nat) : Model →ₗ[ℤ] ℤ × ℤ × ℤ :=
  massRead.prod ((firstCoefficient depth).prod (lastCoefficient depth))

def rebuild (depth : Nat) : (ℤ × ℤ × ℤ) →ₗ[ℤ] Model :=
  (LinearMap.fst ℤ ℤ (ℤ × ℤ)).smulRight (Fock.point depth) +
    ((LinearMap.fst ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ (ℤ × ℤ))).smulRight (effect depth) +
      ((LinearMap.snd ℤ ℤ ℤ).comp (LinearMap.snd ℤ ℤ (ℤ × ℤ))).smulRight (secondEffect depth)

theorem coordinates_apply (depth : Nat) (value : Model) :
    coordinates depth value = (massRead value,
      clockRead value - massRead value * clockRead (Fock.point depth),
      secondRead value - massRead value * secondRead (Fock.point depth) -
        (clockRead value - massRead value * clockRead (Fock.point depth)) * clockRead (Fock.point depth)) := rfl

theorem rebuild_apply (depth : Nat) (value : ℤ × ℤ × ℤ) :
    rebuild depth value = value.1 • Fock.point depth + value.2.1 • effect depth + value.2.2 • secondEffect depth := rfl

theorem rebuild_coordinates (depth : Nat) (value : Model) : rebuild depth (coordinates depth value) = value :=
  (reconstruction depth value).symm

theorem coordinates_rebuild (depth : Nat) (value : ℤ × ℤ × ℤ) : coordinates depth (rebuild depth value) = value := by
  rw [coordinates_apply, rebuild_apply]
  apply Prod.ext
  · simp only [map_add, map_smul, Fock.mass_point, mass_effect, mass_secondEffect,
      smul_eq_mul, mul_one, mul_zero, add_zero]
  apply Prod.ext
  · simp only [map_add, map_smul, Fock.mass_point, mass_effect, mass_secondEffect,
      clock_effect, clock_secondEffect, smul_eq_mul, mul_one, mul_zero, add_zero]
    ring
  · simp only [map_add, map_smul, Fock.mass_point, mass_effect, mass_secondEffect,
      clock_effect, clock_secondEffect, second_effect, second_secondEffect,
      smul_eq_mul, mul_one, mul_zero, add_zero]
    ring

def frame (depth : Nat) : Model ≃ₗ[ℤ] ℤ × ℤ × ℤ :=
  LinearEquiv.ofLinearMap (coordinates depth) (rebuild depth)
    (LinearMap.ext (coordinates_rebuild depth)) (LinearMap.ext (rebuild_coordinates depth))

end
end SourceBinomialClock.Frame
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
