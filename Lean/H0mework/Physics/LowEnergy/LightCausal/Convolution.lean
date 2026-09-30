import H0mework.Physics.LowEnergy.LightCausal.Development
import H0mework.Physics.LowEnergy.LightCausal.Derivative

/-! The generated operator-valued development is the actual causal convolution, including its original source sign. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
open BosonCausal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem metricDevelopment_convolution (momentum : Fin 3 → ℝ) (source : ℝ → E)
    (continuousSource : Continuous source) (time : ℝ) :
    metricDevelopment momentum source time=
      ∫ r in (0 : ℝ)..time, futureMetricKernel momentum (time-r) • source r := by
  have plus : Continuous (fun r : ℝ => Complex.exp ((thetaRate momentum : ℂ)*((time-r : ℝ) : ℂ)) • source r) := by fun_prop
  have minus : Continuous (fun r : ℝ => Complex.exp (-(thetaRate momentum : ℂ)*((time-r : ℝ) : ℂ)) • source r) := by fun_prop
  rw [metricDevelopment,forcedVector_convolution,forcedVector_convolution,
    ← intervalIntegral.integral_sub (plus.intervalIntegrable (μ := volume) 0 time)
      (minus.intervalIntegrable (μ := volume) 0 time),← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  simp only [futureMetricKernel,inverseMetricKernel,mode]
  module

theorem metricDevelopment_causal (momentum : Fin 3 → ℝ) (source : ℝ → E)
    (continuousSource : Continuous source) (time : ℝ) (future : 0≤time) :
    metricDevelopment momentum source time=
      ∫ r in (0 : ℝ)..time, metricSourceKernel momentum (time-r) • source r := by
  rw [metricDevelopment_convolution momentum source continuousSource time]
  apply intervalIntegral.integral_congr
  intro r inside
  dsimp only
  rw [Set.uIcc_of_le future] at inside
  rw [metricSourceKernel_future momentum (time-r) (sub_nonneg.mpr inside.2)]

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
