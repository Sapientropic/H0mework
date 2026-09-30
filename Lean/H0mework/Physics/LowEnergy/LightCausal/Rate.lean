import H0mework.Physics.LowEnergy.LightSpace.Radial
import H0mework.Physics.LowEnergy.BosonCausal.Pair

/-! The actual radial theta root supplies its physical growth rate and the correct causal damping domain. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
open LightSpace LightModes Stage9C.Material.SpinPair
noncomputable section

def thetaRate (momentum : Fin 3 → ℝ) : ℝ :=
  lapse*spinScale*radialMomentum momentum*Real.sqrt ((sourceRoot .axialPhase).root ((radialMomentum momentum)^2))

theorem thetaRate_positive (momentum : Fin 3 → ℝ) (nonzero : momentum≠0) : 0<thetaRate momentum :=
  mul_pos (mul_pos (mul_pos lapse_pos spinScale_pos) (radial_positive momentum nonzero))
    (Real.sqrt_pos.mpr ((root_sign .axialPhase _).1 rfl))

theorem thetaRate_original_clock (momentum : Fin 3 → ℝ) :
    (thetaRate momentum : ℂ)=sourceExponent .axialPhase momentum := by
  simp [thetaRate,sourceExponent,physicalExponent,sourceWave,sourcePower,Complex.ofReal_mul,mul_assoc]

theorem thetaRate_bound (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum ≤ spinScale*LightModes.momentumRadius) :
    thetaRate momentum≤2*(lapse*spinScale)*LightModes.momentumRadius := by
  let q := radialMomentum momentum
  let r := (sourceRoot .axialPhase).root (q^2)
  have qpositive : 0<q := radial_positive momentum nonzero
  have qsmall : q≤LightModes.momentumRadius := by
    exact (le_abs_self q).trans (radial_small momentum small)
  have rpositive : 0<r := (root_sign .axialPhase _).1 rfl
  have rbound := (sourceRoot .axialPhase).window_bound r ((sourceRoot .axialPhase).root_in_window (q^2))
  have rootBound : Real.sqrt r≤2 := by
    have square := Real.sq_sqrt rpositive.le
    nlinarith [Real.sqrt_nonneg r,le_abs_self r]
  change lapse*spinScale*q*Real.sqrt r≤_
  calc
    _ ≤ lapse*spinScale*q*2 := mul_le_mul_of_nonneg_left rootBound (mul_pos (mul_pos lapse_pos spinScale_pos) qpositive).le
    _ ≤ 2*(lapse*spinScale)*LightModes.momentumRadius := by nlinarith [mul_pos lapse_pos spinScale_pos]

def metricResidue (momentum : Fin 3 → ℝ) : ℂ :=
  ((lapse*spinScale : ℝ) : ℂ)*
    (metricNumerator (sourceWave .axialPhase (radialMomentum momentum)) (radialMomentum momentum)/
      axialTimeDerivative (radialMomentum momentum))

theorem metricResidue_nonzero (momentum : Fin 3 → ℝ) (nonzero : momentum≠0)
    (small : Rotation.momentumRadius momentum ≤ spinScale*LightModes.momentumRadius) : metricResidue momentum≠0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos lapse_pos spinScale_pos).ne')
    (generated_metric_pole momentum nonzero small).2

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
