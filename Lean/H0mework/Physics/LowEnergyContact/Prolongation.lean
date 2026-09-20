import H0mework.Physics.LowEnergyContact.Slice

/-! The next scalar time jet forced by the homogeneous slice geometry.
These are exact scalar normal-form statements; complete coupled evolution
still requires the remaining field equations on the same spacetime germ. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Contact.Prolongation
open Stage9C.Material.SpinPair Response.Radial
noncomputable section

def jerk (parameter : ℝ) : ℝ :=
  (2 * (Slice.clock parameter)^2 - 3 * Slice.scaleAcceleration parameter) * Slice.impulse parameter

theorem jerk_formula (parameter : ℝ) :
    jerk parameter = growthRate^2 * Slice.impulse parameter +
      19 * Stress.weight * (Slice.impulse parameter)^3 / 18 := by
  rw [jerk, Slice.clock_squared, growthRate_sq]
  unfold Slice.scaleAcceleration
  ring

def profile (parameter time : ℝ) : ℝ :=
  Slice.impulse parameter * time + jerk parameter * time^3 / 6
def velocity (parameter time : ℝ) : ℝ :=
  Slice.impulse parameter + jerk parameter * time^2 / 2
def acceleration (parameter time : ℝ) : ℝ := jerk parameter * time

theorem first_derivative (parameter time : ℝ) :
    HasDerivAt (profile parameter) (velocity parameter time) time := by
  unfold profile velocity
  convert! ((hasDerivAt_id time).const_mul (Slice.impulse parameter)).add
    (((hasDerivAt_id time).pow 3).const_mul (jerk parameter) |>.div_const 6) using 1
  all_goals first | rfl | (simp only [id_eq]; ring)

theorem second_derivative (parameter time : ℝ) :
    HasDerivAt (velocity parameter) (acceleration parameter time) time := by
  unfold velocity acceleration
  convert! ((((hasDerivAt_id time).pow 2).const_mul (jerk parameter)).div_const 2).const_add
    (Slice.impulse parameter) using 1
  all_goals first | rfl | (simp only [id_eq]; ring)

def residual (parameter time : ℝ) : ℝ :=
  acceleration parameter time + 3 * Slice.scaleAcceleration parameter * time * velocity parameter time -
    2 * (Slice.clock parameter)^2 * profile parameter time

/-- The generated cubic cancels the linear time coefficient of the scalar equation. -/
theorem residual_order_three (parameter time : ℝ) :
    residual parameter time =
      (3 * Slice.scaleAcceleration parameter / 2 - (Slice.clock parameter)^2 / 3) *
        jerk parameter * time^3 := by
  unfold residual acceleration velocity profile jerk
  ring

def oldResidual (parameter time : ℝ) : ℝ :=
  parameter * growthRate^2 * Real.sinh (growthRate * time) +
    3 * Slice.scaleAcceleration parameter * time * parameter * growthRate * Real.cosh (growthRate * time) -
    2 * (Slice.clock parameter)^2 * parameter * Real.sinh (growthRate * time)

/-- The old sinh profile already leaves an exact cubic-amplitude defect. -/
theorem old_residual_derivative (parameter : ℝ) :
    HasDerivAt (oldResidual parameter)
      (-19 * Stress.weight * (Slice.impulse parameter)^3 / 18) 0 := by
  have linear := (hasDerivAt_id (0 : ℝ)).const_mul growthRate
  have sinh := linear.sinh
  have cosh := linear.cosh
  have computed := ((sinh.const_mul (parameter * growthRate^2)).add
    ((((hasDerivAt_id (0 : ℝ)).const_mul (3 * Slice.scaleAcceleration parameter)).mul_const parameter
      |>.mul_const growthRate).mul cosh)).sub
    (sinh.const_mul (2 * (Slice.clock parameter)^2 * parameter))
  convert! computed using 1
  simp only [id_eq, mul_zero, Real.sinh_zero, Real.cosh_zero, mul_one, zero_mul,
    add_zero]
  rw [Slice.clock_squared, growthRate_sq]
  unfold Slice.scaleAcceleration Slice.impulse
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Contact.Prolongation
