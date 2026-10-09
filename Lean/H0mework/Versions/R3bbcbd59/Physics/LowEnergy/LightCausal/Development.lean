import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.LightCausal.Metric
import H0mework.Physics.LowEnergy.LightCausal.Forcing

/-! The true theta pole channel consumes a vector or operator current and generates its second-order forced response. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def metricDevelopment (momentum : Fin 3 → ℝ) (source : ℝ → E) (time : ℝ) : E :=
  (-metricResidue momentum) • (forcedVector (thetaRate momentum) source time-forcedVector (-(thetaRate momentum : ℂ)) source time)

def metricVelocity (momentum : Fin 3 → ℝ) (source : ℝ → E) (time : ℝ) : E :=
  (-metricResidue momentum*(thetaRate momentum : ℂ)) •
    (forcedVector (thetaRate momentum) source time+forcedVector (-(thetaRate momentum : ℂ)) source time)

omit [CompleteSpace E] in
theorem metricDevelopment_initial (momentum : Fin 3 → ℝ) (source : ℝ → E) :
    metricDevelopment momentum source 0=0 ∧ metricVelocity momentum source 0=0 := by
  simp [metricDevelopment,metricVelocity,forcedVector_initial]

theorem metricDevelopment_derivative (momentum : Fin 3 → ℝ) (source : ℝ → E)
    (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (metricDevelopment momentum source) (metricVelocity momentum source time) time := by
  have plus := forcedVector_derivative (thetaRate momentum) source continuousSource time
  have minus := forcedVector_derivative (-(thetaRate momentum : ℂ)) source continuousSource time
  have differentiated := (plus.sub minus).const_smul (-metricResidue momentum)
  convert! differentiated using 1
  simp only [metricVelocity]
  module

theorem metricVelocity_derivative (momentum : Fin 3 → ℝ) (source : ℝ → E)
    (continuousSource : Continuous source) (time : ℝ) :
    HasDerivAt (metricVelocity momentum source)
      (((thetaRate momentum : ℂ)^2) • metricDevelopment momentum source time-
        (2*metricResidue momentum*(thetaRate momentum : ℂ)) • source time) time := by
  have plus := forcedVector_derivative (thetaRate momentum) source continuousSource time
  have minus := forcedVector_derivative (-(thetaRate momentum : ℂ)) source continuousSource time
  have differentiated := (plus.add minus).const_smul (-metricResidue momentum*(thetaRate momentum : ℂ))
  convert! differentiated using 1
  simp only [metricDevelopment]
  module

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
