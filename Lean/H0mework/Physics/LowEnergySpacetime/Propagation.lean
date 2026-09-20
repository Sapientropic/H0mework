import H0mework.Physics.LowEnergySpacetime.Oscillation

/-! Unit-initial-velocity Fourier propagation across all three source momentum regimes. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
open StageNineDynamicBreakingVacuum
open StageNineDiracDualFormNativeScalarVariation
open scoped ContDiff
noncomputable section

def fundamentalTime (momentum : Fin 3 → ℝ) (time : ℝ) : ℝ :=
  if momentumSquared momentum < 2 then Real.sinh (radialRate momentum*time)/radialRate momentum
  else if momentumSquared momentum = 2 then time
  else Real.sin (oscillationRate momentum*time)/oscillationRate momentum

def fundamentalVelocity (momentum : Fin 3 → ℝ) (time : ℝ) : ℝ :=
  if momentumSquared momentum < 2 then Real.cosh (radialRate momentum*time)
  else if momentumSquared momentum = 2 then 1
  else Real.cos (oscillationRate momentum*time)

def fundamentalAcceleration (momentum : Fin 3 → ℝ) (time : ℝ) : ℝ :=
  if momentumSquared momentum < 2 then radialRate momentum*Real.sinh (radialRate momentum*time)
  else if momentumSquared momentum = 2 then 0
  else -oscillationRate momentum*Real.sin (oscillationRate momentum*time)

theorem fundamentalTime_first (momentum : Fin 3 → ℝ) (time : ℝ) :
    HasDerivAt (fundamentalTime momentum) (fundamentalVelocity momentum time) time := by
  unfold fundamentalTime fundamentalVelocity
  by_cases below : momentumSquared momentum < 2
  · simp only [if_pos below]
    convert! ((((hasDerivAt_id time).const_mul (radialRate momentum)).sinh).div_const (radialRate momentum)) using 1
    simp only [id_eq, mul_one]
    field_simp [ne_of_gt (radialRate_positive momentum below)]
  · by_cases critical : momentumSquared momentum = 2
    · simp only [if_neg below, if_pos critical]
      exact hasDerivAt_id time
    · have above : 2 < momentumSquared momentum := lt_of_le_of_ne (le_of_not_gt below) (Ne.symm critical)
      simp only [if_neg below, if_neg critical]
      convert! ((((hasDerivAt_id time).const_mul (oscillationRate momentum)).sin).div_const (oscillationRate momentum)) using 1
      simp only [id_eq, mul_one]
      field_simp [ne_of_gt (oscillationRate_positive momentum above)]

theorem fundamentalTime_second (momentum : Fin 3 → ℝ) (time : ℝ) :
    HasDerivAt (fundamentalVelocity momentum) (fundamentalAcceleration momentum time) time := by
  unfold fundamentalVelocity fundamentalAcceleration
  by_cases below : momentumSquared momentum < 2
  · simp only [if_pos below]
    convert! (((hasDerivAt_id time).const_mul (radialRate momentum)).cosh) using 1
    simp
    ring
  · by_cases critical : momentumSquared momentum = 2
    · simp only [if_neg below, if_pos critical]
      exact hasDerivAt_const time (1:ℝ)
    · simp only [if_neg below, if_neg critical]
      convert! (((hasDerivAt_id time).const_mul (oscillationRate momentum)).cos) using 1
      simp
      ring

theorem fundamentalTime_smooth (momentum : Fin 3 → ℝ) : ContDiff ℝ ∞ (fundamentalTime momentum) := by
  unfold fundamentalTime
  split_ifs <;> fun_prop

theorem fundamentalVelocity_smooth (momentum : Fin 3 → ℝ) : ContDiff ℝ ∞ (fundamentalVelocity momentum) := by
  unfold fundamentalVelocity
  split_ifs <;> fun_prop

theorem fundamentalTime_equation (momentum : Fin 3 → ℝ) (time : ℝ) :
    fundamentalAcceleration momentum time/lapse^2+
      (momentumSquared momentum-2)*fundamentalTime momentum time = 0 := by
  by_cases below : momentumSquared momentum < 2
  · simp only [fundamentalAcceleration, fundamentalTime, if_pos below]
    have coefficient : radialRate momentum/lapse^2+(momentumSquared momentum-2)/radialRate momentum = 0 := by
      field_simp [ne_of_gt lapse_pos, ne_of_gt (radialRate_positive momentum below)]
      nlinarith [radialRate_squared momentum below.le]
    calc
      _ = (radialRate momentum/lapse^2+(momentumSquared momentum-2)/radialRate momentum)*
          Real.sinh (radialRate momentum*time) := by ring
      _ = 0 := by rw [coefficient, zero_mul]
  · by_cases critical : momentumSquared momentum = 2
    · simp [fundamentalAcceleration, fundamentalTime, critical]
    · have above : 2 < momentumSquared momentum := lt_of_le_of_ne (le_of_not_gt below) (Ne.symm critical)
      simp only [fundamentalAcceleration, fundamentalTime, if_neg below, if_neg critical]
      have coefficient : -oscillationRate momentum/lapse^2+
          (momentumSquared momentum-2)/oscillationRate momentum = 0 := by
        field_simp [ne_of_gt lapse_pos, ne_of_gt (oscillationRate_positive momentum above)]
        nlinarith [oscillationRate_squared momentum above.le]
      calc
        _ = (-oscillationRate momentum/lapse^2+(momentumSquared momentum-2)/oscillationRate momentum)*
            Real.sin (oscillationRate momentum*time) := by ring
        _ = 0 := by rw [coefficient, zero_mul]

theorem fundamentalTime_zero (momentum : Fin 3 → ℝ) : fundamentalTime momentum 0 = 0 := by
  simp [fundamentalTime]

theorem fundamentalVelocity_zero (momentum : Fin 3 → ℝ) : fundamentalVelocity momentum 0 = 1 := by
  simp [fundamentalVelocity]

def fundamentalWave (momentum : Fin 3 → ℝ) : BasePoint → ℝ := separatedWave (fundamentalTime momentum) momentum

theorem fundamentalWave_smooth (momentum : Fin 3 → ℝ) : ContDiff ℝ ∞ (fundamentalWave momentum) :=
  separatedWave_smooth _ _ (fundamentalTime_smooth momentum)

theorem fundamentalWave_twice (momentum : Fin 3 → ℝ) (mu : LorentzianIndex) :
    Differentiable ℝ (coordinateDerivative (fundamentalWave momentum) mu) :=
  separatedWave_twice _ _ _ (fundamentalTime_first momentum)
    (fundamentalTime_smooth momentum) (fundamentalVelocity_smooth momentum) mu

theorem fundamentalWave_operator (momentum : Fin 3 → ℝ) (point : BasePoint) :
    radialOperator (fundamentalWave momentum) point = 0 := by
  rw [fundamentalWave, separatedWave_operator _ _ _ _
    (fundamentalTime_first momentum) (fundamentalTime_second momentum), fundamentalTime_equation, zero_mul]

theorem fundamentalWave_scalar_zero (momentum : Fin 3 → ℝ) (parameter : ℝ)
    (point : BasePoint) (test : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration (fundamentalWave momentum) parameter) test point = 0 := by
  rw [scalar_euler (fundamentalWave momentum) parameter point
    ((fundamentalWave_smooth momentum).differentiable (by norm_num))
    (fun mu => fundamentalWave_twice momentum mu point), fundamentalWave_operator]
  ring

theorem fundamentalWave_initial (momentum : Fin 3 → ℝ) (point : BasePoint) (initial : point 0 = 0) :
    fundamentalWave momentum point = 0 := by
  simp [fundamentalWave, separatedWave, initial, fundamentalTime_zero]

theorem fundamentalWave_initial_speed (momentum : Fin 3 → ℝ) (point : BasePoint) (initial : point 0 = 0) :
    coordinateDerivative (fundamentalWave momentum) 0 point = Real.cos (spatialPhase momentum point) := by
  rw [fundamentalWave, separatedWave_time _ _ _ (fundamentalTime_first momentum), initial,
    fundamentalVelocity_zero, one_mul]

theorem fundamentalWave_below (momentum : Fin 3 → ℝ) (below : momentumSquared momentum < 2) (point : BasePoint) :
    fundamentalWave momentum point =
      Real.sinh (radialRate momentum*point 0)/radialRate momentum*Real.cos (spatialPhase momentum point) := by
  simp [fundamentalWave, separatedWave, fundamentalTime, below]

theorem fundamentalWave_critical (momentum : Fin 3 → ℝ) (critical : momentumSquared momentum = 2) (point : BasePoint) :
    fundamentalWave momentum point = point 0*Real.cos (spatialPhase momentum point) := by
  simp [fundamentalWave, separatedWave, fundamentalTime, critical]

theorem fundamentalWave_above (momentum : Fin 3 → ℝ) (above : 2 < momentumSquared momentum) (point : BasePoint) :
    fundamentalWave momentum point =
      Real.sin (oscillationRate momentum*point 0)/oscillationRate momentum*Real.cos (spatialPhase momentum point) := by
  have below : ¬momentumSquared momentum < 2 := by linarith
  have critical : ¬momentumSquared momentum = 2 := by linarith
  simp [fundamentalWave, separatedWave, fundamentalTime, below, critical]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
