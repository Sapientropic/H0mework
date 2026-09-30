import H0mework.Physics.LowEnergy.DrivenInteraction.Polynomial
import H0mework.Physics.LowEnergy.LightInteraction.Pole

/-! All four growth pairings use their own source derivatives; the same-growth pair has a different exact numerator and the same nonzero infrared limit. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
open LightModes LightInteraction Filter Topology Stage9C.Material.SpinPair
noncomputable section

def growthNumerator (z : ℂ) (q : ℝ) : ℂ :=
  (4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*growthPolynomial (z^2) ((q : ℂ)^2)

def growthCoupling (q : ℝ) : ℝ := responseScale*growthNormal q/(axialRoot q*(axialDerivative q)^2)
def physicalGrowthCoupling (q : ℝ) : ℝ := (lapse*spinScale)^2*growthCoupling q

theorem growth_coupling_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<growthCoupling q :=
  div_pos (mul_pos response_scale_positive (growth_normal_positive q small))
    (mul_pos (axial_root_positive q) (sq_pos_of_pos (axial_derivative_positive q small)))

theorem growth_numerator_root (q : ℝ) :
    growthNumerator (sourceWave .axialPhase q) q=
      (4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
        ((q^2*growthNormal q : ℝ) : ℂ) := by
  unfold growthNumerator
  rw [source_wave_square]
  simp only [sourcePower,pow_one]
  rw [Complex.ofReal_mul,Complex.ofReal_pow,growth_polynomial_scaling]
  rw [show (q : ℂ)^2=((q^2 : ℝ) : ℂ) by norm_cast,complexValue_real,complexValue_real]
  simp only [growthNormal,currentNormal,axialRoot,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat]

theorem original_growth_residue (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    growthNumerator (sourceWave .axialPhase q) q/(axialTimeDerivative q)^2=(growthCoupling q : ℂ) := by
  rw [growth_numerator_root,source_time_derivative_squared q small nonzero]
  have hn : (q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have hc : (sourceCoefficient .axialPhase : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (source_coefficient_nonzero .axialPhase)
  have hr : (axialRoot q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (axial_root_positive q).ne'
  have hd : (axialDerivative q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (axial_derivative_positive q small).ne'
  unfold growthCoupling
  push_cast
  field_simp [hn,hc,hr,hd]

theorem physical_growth_coupling_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<physicalGrowthCoupling q :=
  mul_pos (sq_pos_of_pos (mul_pos lapse_pos spinScale_pos)) (growth_coupling_positive q small)

theorem growth_coupling_limit : Tendsto growthCoupling (𝓝 0) (𝓝 responseScale) := by
  have denom := axial_root_limit.mul (axial_derivative_limit.pow 2)
  have generated := (growth_normal_limit.const_mul responseScale).div denom (by norm_num)
  convert! generated using 1
  simp

theorem physical_growth_coupling_limit :
    Tendsto physicalGrowthCoupling (𝓝 0) (𝓝 (486*Real.sqrt 15/390625)) := by
  have generated := growth_coupling_limit.const_mul ((lapse*spinScale)^2)
  have scale : (lapse*spinScale)^2*responseScale=486*Real.sqrt 15/390625 := by
    rw [mul_pow,lapse_sq,spinScale_sq]
    unfold responseScale
    ring
  rw [scale] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
