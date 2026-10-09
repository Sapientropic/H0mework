import H0mework.Physics.LowEnergy.BosonCausal.Response

/-! The original source response is a true retarded convolution plus its
instantaneous term; no distribution endpoint convention is hidden in the integral. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory
noncomputable section

theorem pairForced_convolution (rate : ℂ) (source : ℝ → ℂ)
    (regular : Continuous source) (time : ℝ) :
    pairForced rate source time =
      ∫ s : ℝ in (0 : ℝ)..time, pairKernel rate (time-s)*source s := by
  have first : Continuous (fun s : ℝ => Complex.exp (rate*((time-s : ℝ) : ℂ))*source s) := by fun_prop
  have second : Continuous (fun s : ℝ => Complex.exp (-rate*((time-s : ℝ) : ℂ))*source s) := by fun_prop
  rw [pairForced,forcedMode_convolution,forcedMode_convolution,
    ← intervalIntegral.integral_sub (first.intervalIntegrable (μ := volume) 0 time)
      (second.intervalIntegrable (μ := volume) 0 time),← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [pairKernel,mode]
  ring

theorem responseTo_convolution (source : ℝ → ℂ) (regular : Continuous source) (time : ℝ) :
    responseTo source time=contact*source time+
      ∫ s : ℝ in (0 : ℝ)..time, memory (time-s)*source s := by
  have continuousPair (rate : ℂ) : Continuous (fun s : ℝ => pairKernel rate (time-s)*source s) := by
    unfold pairKernel mode
    fun_prop
  have first := ((continuousPair (Complex.I*(oscillation : ℂ))).const_mul oscillationWeight).intervalIntegrable (μ := volume) 0 time
  have second := ((continuousPair (growth : ℂ)).const_mul growthWeight).intervalIntegrable (μ := volume) 0 time
  rw [responseTo,pairForced_convolution _ _ regular,pairForced_convolution _ _ regular,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,add_assoc,
    ← intervalIntegral.integral_add first second]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [memory]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
