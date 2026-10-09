import H0mework.Physics.LowEnergy.LightCausal.Forcing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Rescaling the actual time integral generates a jointly continuous slope, including time zero, before momentum integration. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open LightCausal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def responseAverage (rate : ℂ) (source : ℝ → E) (time : ℝ) : E :=
  ∫ parameter in (0 : ℝ)..1,
    Complex.exp (rate*((time-time*parameter : ℝ) : ℂ)) • source (time*parameter)

omit [CompleteSpace E] in
theorem forcedVector_average (rate : ℂ) (source : ℝ → E) (time : ℝ) :
    forcedVector rate source time=time • responseAverage rate source time := by
  rw [forcedVector_convolution]
  have actual := intervalIntegral.smul_integral_comp_mul_left
    (fun r : ℝ => Complex.exp (rate*((time-r : ℝ) : ℂ)) • source r) (a := 0) (b := 1) time
  simpa only [mul_zero,mul_one,responseAverage] using actual.symm

theorem responseAverage_initial (rate : ℂ) (source : ℝ → E) : responseAverage rate source 0=source 0 := by
  simp [responseAverage]

omit [CompleteSpace E] in
theorem responseAverage_continuous {X : Type*} [TopologicalSpace X]
    (rate : X → ℂ) (continuousRate : Continuous rate)
    (source : X → ℝ → E) (continuousSource : Continuous source.uncurry) :
    Continuous (fun pair : X×ℝ => responseAverage (rate pair.1) (source pair.1) pair.2) := by
  unfold responseAverage
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have integrandSource : Continuous (fun pair : (X×ℝ)×ℝ => source pair.1.1 (pair.1.2*pair.2)) :=
    continuousSource.comp (continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd))
  have exponent : Continuous (fun pair : (X×ℝ)×ℝ =>
      rate pair.1.1*((pair.1.2-pair.1.2*pair.2 : ℝ) : ℂ)) := by fun_prop
  exact (Complex.continuous_exp.comp exponent).smul integrandSource

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
