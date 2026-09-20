import H0mework.Physics.LowEnergySpacetime.Modes

/-! The open spatial growth band, in the unchanged source coordinates. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineDiracDualFormNativeScalarVariation Stage9C.Dynamics.Homogeneous Response.Radial
noncomputable section

def momentumSquared (momentum : Fin 3 → ℝ) : ℝ := ∑ axis, (momentum axis)^2
def radialRate (momentum : Fin 3 → ℝ) : ℝ := lapse*Real.sqrt (2-momentumSquared momentum)
def growingWave (momentum : Fin 3 → ℝ) : BasePoint → ℝ := radialWave (radialRate momentum) momentum

theorem radialRate_positive (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum < 2) :
    0 < radialRate momentum := mul_pos lapse_pos (Real.sqrt_pos.mpr (by linarith))

theorem radialRate_squared (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum ≤ 2) :
    (radialRate momentum)^2 = lapse^2*(2-momentumSquared momentum) := by
  rw [radialRate, mul_pow, Real.sq_sqrt (by linarith)]

theorem radialRate_zero : radialRate 0 = growthRate := by
  have inside : momentumSquared (0 : Fin 3 → ℝ) < 2 := by norm_num [momentumSquared]
  have positive := radialRate_positive 0 inside
  have square := radialRate_squared 0 inside.le
  simp only [momentumSquared, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, sub_zero] at square
  have original := growthRate_sq
  nlinarith [growthRate_pos]

theorem growingWave_operator (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum ≤ 2)
    (point : BasePoint) : radialOperator (growingWave momentum) point = 0 := by
  rw [growingWave, radialWave_operator, radialRate_squared momentum inside]
  change (lapse^2*(2-momentumSquared momentum)/lapse^2+momentumSquared momentum-2)*_ = 0
  field_simp [ne_of_gt lapse_pos]
  ring

theorem growingWave_scalar_zero (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum ≤ 2)
    (parameter : ℝ) (point : BasePoint) (test : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration (growingWave momentum) parameter) test point = 0 := by
  rw [scalar_euler (growingWave momentum) parameter point
    ((radialWave_smooth _ _).differentiable (by norm_num)) (fun mu => radialWave_twice _ _ mu point),
    growingWave_operator momentum inside]
  ring

theorem growingWave_initial (momentum : Fin 3 → ℝ) (point : BasePoint) (initial : point 0 = 0) :
    growingWave momentum point = 0 := by simp [growingWave, radialWave, initial]

theorem growingWave_initial_speed (momentum : Fin 3 → ℝ) :
    coordinateDerivative (growingWave momentum) 0 0 = radialRate momentum := by
  rw [growingWave, radialWave_time]
  simp

theorem growingWave_nonzero (momentum : Fin 3 → ℝ) (inside : momentumSquared momentum < 2) :
    growingWave momentum ≠ 0 := by
  intro zero
  have speed := growingWave_initial_speed momentum
  rw [zero] at speed
  have : radialRate momentum = 0 := by
    simpa [coordinateDerivative, fieldDirectionalDerivative] using speed.symm
  exact (ne_of_gt (radialRate_positive momentum inside)) this

theorem growingWave_scalar_contact (momentum : Fin 3 → ℝ) (parameter : ℝ)
    (point : BasePoint) (initial : point 0 = 0) :
    (configuration (growingWave momentum) parameter).scalar point = actual.scalar point := by
  simp [configuration, growingWave_initial momentum point initial, actual_scalar, direction]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
