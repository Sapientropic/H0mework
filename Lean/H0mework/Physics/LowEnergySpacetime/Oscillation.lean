import H0mework.Physics.LowEnergySpacetime.Dispersion

/-! Actual spacetime derivatives for a separated temporal profile and the high-momentum branch. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open scoped ContDiff
noncomputable section

def separatedWave (temporal : ℝ → ℝ) (momentum : Fin 3 → ℝ) (point : BasePoint) : ℝ :=
  temporal (point 0)*Real.cos (spatialPhase momentum point)

theorem separatedWave_smooth (temporal : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (smooth : ContDiff ℝ ∞ temporal) : ContDiff ℝ ∞ (separatedWave temporal momentum) := by
  unfold separatedWave
  fun_prop

theorem separatedWave_time (temporal velocity : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (derivative : ∀ time, HasDerivAt temporal (velocity time) time) (point : BasePoint) :
    coordinateDerivative (separatedWave temporal momentum) 0 point =
      velocity (point 0)*Real.cos (spatialPhase momentum point) := by
  have composed := (derivative (point 0)).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  have total := composed.mul (((spatialPhase momentum).hasFDerivAt (x := point)).cos)
  change HasFDerivAt (separatedWave temporal momentum) _ point at total
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [total.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_time]
  simp [coordinateDirection]
  ring

theorem separatedWave_space (temporal velocity : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (derivative : ∀ time, HasDerivAt temporal (velocity time) time) (point : BasePoint) (axis : Fin 3) :
    coordinateDerivative (separatedWave temporal momentum) axis.succ point =
      -momentum axis*temporal (point 0)*Real.sin (spatialPhase momentum point) := by
  have composed := (derivative (point 0)).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  have total := composed.mul (((spatialPhase momentum).hasFDerivAt (x := point)).cos)
  change HasFDerivAt (separatedWave temporal momentum) _ point at total
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [total.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_space]
  simp [coordinateDirection, Fin.succ_ne_zero]
  ring

theorem separatedWave_time_time (temporal velocity acceleration : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (first : ∀ time, HasDerivAt temporal (velocity time) time)
    (second : ∀ time, HasDerivAt velocity (acceleration time) time) (point : BasePoint) :
    coordinateDerivative (coordinateDerivative (separatedWave temporal momentum) 0) 0 point =
      acceleration (point 0)*Real.cos (spatialPhase momentum point) := by
  rw [funext (separatedWave_time temporal velocity momentum first)]
  exact separatedWave_time velocity acceleration momentum second point

theorem separatedWave_space_space (temporal velocity : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (first : ∀ time, HasDerivAt temporal (velocity time) time) (point : BasePoint) (axis : Fin 3) :
    coordinateDerivative (coordinateDerivative (separatedWave temporal momentum) axis.succ) axis.succ point =
      -(momentum axis)^2*separatedWave temporal momentum point := by
  rw [funext (fun p => separatedWave_space temporal velocity momentum first p axis)]
  have composed := (first (point 0)).hasFDerivAt.comp point
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
  have derivative := (composed.const_mul (-momentum axis)).mul
    (((spatialPhase momentum).hasFDerivAt (x := point)).sin)
  change HasFDerivAt (fun p : BasePoint => -momentum axis*temporal (p 0)*Real.sin (spatialPhase momentum p)) _ point at derivative
  unfold coordinateDerivative fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, spatialPhase_space]
  simp [coordinateDirection, separatedWave, Fin.succ_ne_zero]
  ring

theorem separatedWave_twice (temporal velocity : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (first : ∀ time, HasDerivAt temporal (velocity time) time)
    (smooth : ContDiff ℝ ∞ temporal) (velocitySmooth : ContDiff ℝ ∞ velocity) (mu : LorentzianIndex) :
    Differentiable ℝ (coordinateDerivative (separatedWave temporal momentum) mu) := by
  have temporalDifferentiable := smooth.differentiable (by norm_num)
  have velocityDifferentiable := velocitySmooth.differentiable (by norm_num)
  refine Fin.cases ?_ (fun axis => ?_) mu
  · rw [funext (separatedWave_time temporal velocity momentum first)]
    fun_prop
  · rw [funext (fun p => separatedWave_space temporal velocity momentum first p axis)]
    fun_prop

theorem separatedWave_operator (temporal velocity acceleration : ℝ → ℝ) (momentum : Fin 3 → ℝ)
    (first : ∀ time, HasDerivAt temporal (velocity time) time)
    (second : ∀ time, HasDerivAt velocity (acceleration time) time) (point : BasePoint) :
    radialOperator (separatedWave temporal momentum) point =
      (acceleration (point 0)/lapse^2+(momentumSquared momentum-2)*temporal (point 0))*
        Real.cos (spatialPhase momentum point) := by
  unfold radialOperator
  rw [separatedWave_time_time temporal velocity acceleration momentum first second]
  simp_rw [separatedWave_space_space temporal velocity momentum first]
  rw [← Finset.sum_mul]
  simp only [Finset.sum_neg_distrib]
  unfold separatedWave momentumSquared
  ring

def oscillationRate (momentum : Fin 3 → ℝ) : ℝ := lapse*Real.sqrt (momentumSquared momentum-2)

theorem oscillationRate_positive (momentum : Fin 3 → ℝ) (above : 2 < momentumSquared momentum) :
    0 < oscillationRate momentum := mul_pos lapse_pos (Real.sqrt_pos.mpr (by linarith))

theorem oscillationRate_squared (momentum : Fin 3 → ℝ) (above : 2 ≤ momentumSquared momentum) :
    oscillationRate momentum^2 = lapse^2*(momentumSquared momentum-2) := by
  rw [oscillationRate, mul_pow, Real.sq_sqrt (by linarith)]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
