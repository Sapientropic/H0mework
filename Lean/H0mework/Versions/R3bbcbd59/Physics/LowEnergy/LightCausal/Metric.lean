import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.LightCausal.Rate

/-! The actual positive and negative theta residues generate a causal metric pole channel, with its original source sign. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
open BosonCausal
noncomputable section

def inverseMetricKernel (momentum : Fin 3 → ℝ) (time : ℝ) : ℂ :=
  metricResidue momentum*(mode (thetaRate momentum) time-mode (-thetaRate momentum) time)

def metricSourceKernel (momentum : Fin 3 → ℝ) (time : ℝ) : ℂ :=
  if 0≤time then -inverseMetricKernel momentum time else 0

def inverseMetricPole (momentum : Fin 3 → ℝ) (parameter : ℂ) : ℂ :=
  metricResidue momentum*((parameter-thetaRate momentum)⁻¹-(parameter+thetaRate momentum)⁻¹)

theorem metricSourceKernel_past (momentum : Fin 3 → ℝ) (time : ℝ) (past : time<0) :
    metricSourceKernel momentum time=0 := by simp [metricSourceKernel,not_le.mpr past]

theorem metricSourceKernel_initial (momentum : Fin 3 → ℝ) : metricSourceKernel momentum 0=0 := by
  simp [metricSourceKernel,inverseMetricKernel,mode]

theorem inverseMetricKernel_hyperbolic (momentum : Fin 3 → ℝ) (time : ℝ) :
    inverseMetricKernel momentum time=2*metricResidue momentum*Complex.sinh ((thetaRate momentum : ℂ)*(time : ℂ)) := by
  simp only [inverseMetricKernel,mode,Complex.sinh,neg_mul]
  ring

theorem inverseMetricKernel_integrable (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (energy damping : ℝ) (decay : thetaRate momentum<damping) :
    IntegrableOn (fun t => weight energy damping t*inverseMetricKernel momentum t) (Set.Ioi 0) := by
  have plus : (thetaRate momentum : ℂ).re<damping := decay
  have minus : (-(thetaRate momentum : ℂ)).re<damping := by
    simp only [Complex.neg_re,Complex.ofReal_re]
    linarith [thetaRate_positive momentum nonzero]
  have difference := ((mode_integrable _ energy damping plus).sub (mode_integrable _ energy damping minus)).const_mul
    (metricResidue momentum)
  change Integrable (fun t : ℝ => weight energy damping t*inverseMetricKernel momentum t) (volume.restrict (Set.Ioi 0))
  convert! difference using 1
  funext t
  simp only [inverseMetricKernel,Pi.sub_apply]
  ring

theorem inverseMetricKernel_transform (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (energy damping : ℝ) (decay : thetaRate momentum<damping) :
    (∫ t : ℝ in Set.Ioi 0, weight energy damping t*inverseMetricKernel momentum t)=
      inverseMetricPole momentum (laplaceParameter energy damping) := by
  have plus : (thetaRate momentum : ℂ).re<damping := decay
  have minus : (-(thetaRate momentum : ℂ)).re<damping := by
    simp only [Complex.neg_re,Complex.ofReal_re]
    linarith [thetaRate_positive momentum nonzero]
  have point (t : ℝ) : weight energy damping t*inverseMetricKernel momentum t=
      metricResidue momentum*(weight energy damping t*mode (thetaRate momentum) t-
        weight energy damping t*mode (-thetaRate momentum) t) := by unfold inverseMetricKernel; ring
  simp_rw [point]
  rw [integral_const_mul,integral_sub (mode_integrable _ energy damping plus)
    (mode_integrable _ energy damping minus),mode_transform _ energy damping plus,mode_transform _ energy damping minus]
  simp only [inverseMetricPole,sub_neg_eq_add]

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
