import H0mework.Physics.LowEnergy.LightCausal.Metric
import H0mework.Physics.LowEnergy.LightCausal.Reality
import H0mework.Physics.LowEnergy.LightCausal.Forcing

/-! The smooth future profile has a nonzero initial slope; its zero-past extension is not assigned a two-sided derivative at the switch. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
open BosonCausal Stage9C.Material.SpinPair
noncomputable section

def futureMetricKernel (momentum : Fin 3 → ℝ) (time : ℝ) : ℂ :=
  -inverseMetricKernel momentum time

theorem futureMetricKernel_real (momentum : Fin 3 → ℝ) (time : ℝ) :
    futureMetricKernel momentum time=
      ((-2*metricResidueReal momentum*Real.sinh (thetaRate momentum*time) : ℝ) : ℂ) := by
  rw [futureMetricKernel,inverseMetricKernel_hyperbolic,← metricResidueReal_cast]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,Complex.ofReal_sinh]
  ring

theorem futureMetricKernel_derivative (momentum : Fin 3 → ℝ) (time : ℝ) :
    HasDerivAt (futureMetricKernel momentum)
      (-metricResidue momentum*(thetaRate momentum : ℂ)*
        (mode (thetaRate momentum) time+mode (-(thetaRate momentum : ℂ)) time)) time := by
  have plus := mode_derivative (thetaRate momentum) time
  have minus := mode_derivative (-(thetaRate momentum : ℂ)) time
  have generated := ((plus.sub minus).const_mul (metricResidue momentum)).neg
  convert! generated using 1
  simp only [mode]
  ring

theorem futureMetricKernel_initial (momentum : Fin 3 → ℝ) :
    futureMetricKernel momentum 0=0 ∧
      HasDerivAt (futureMetricKernel momentum)
        (-2*metricResidue momentum*(thetaRate momentum : ℂ)) 0 := by
  constructor
  · simp [futureMetricKernel,inverseMetricKernel,mode]
  · convert! futureMetricKernel_derivative momentum 0 using 1
    simp [mode]
    ring

theorem futureMetricKernel_slope_nonzero (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum ≤ spinScale*LightModes.momentumRadius) :
    -2*metricResidue momentum*(thetaRate momentum : ℂ)≠0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (metricResidue_nonzero momentum nonzero small))
    (Complex.ofReal_ne_zero.mpr (thetaRate_positive momentum nonzero).ne')

theorem metricSourceKernel_future (momentum : Fin 3 → ℝ) (time : ℝ) (future : 0≤time) :
    metricSourceKernel momentum time=futureMetricKernel momentum time := by
  simp [metricSourceKernel,futureMetricKernel,future]

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
