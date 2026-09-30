import H0mework.Physics.LowEnergy.PacketField.Polynomial
import H0mework.Physics.LowEnergy.VertexTensor.Continuity

/-! The original own-frequency derivative removes the generated radial factor
in every primitive-field numerator. No individual pole-field L² bound is assumed. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open LightModes LightInteraction DrivenInteraction VertexTensor Stage9C.Material.SpinPair
noncomputable section

def poleDenominator (sign : Bool) (q : ℝ) : ℂ :=
  2*(sourceCoefficient .axialPhase : ℂ)*growthSign sign*(Real.sqrt (axialRoot q) : ℂ)*(axialDerivative q : ℂ)

def poleValue (terms : List PoleTerm) (sign : Bool) (orientation q : ℝ) : ℂ :=
  (lapse*spinScale : ℂ)*
    reducedPolynomial terms (growthSign sign*(Real.sqrt (axialRoot q) : ℂ)) orientation q/poleDenominator sign q

theorem poleDenominator_nonzero (sign : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) :
    poleDenominator sign q≠0 := by
  have coefficient := Complex.ofReal_ne_zero.mpr (source_coefficient_nonzero .axialPhase)
  have root := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (axial_root_positive q)).ne'
  have derivative := Complex.ofReal_ne_zero.mpr (axial_derivative_positive q small).ne'
  have growth : growthSign sign≠0 := by cases sign <;> norm_num [growthSign]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) coefficient) growth) root) derivative

theorem poleDenominator_source (sign : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    growthSign sign*axialTimeDerivative q=(q : ℂ)*poleDenominator sign q := by
  rw [source_time_derivative q small nonzero]
  have wave : sourceWave .axialPhase q=(q : ℂ)*(Real.sqrt (axialRoot q) : ℂ) := by
    simp [sourceWave,sourcePower,axialRoot]
  rw [wave,poleDenominator]
  ring

theorem poleValue_source (terms : List PoleTerm) (sign : Bool) (orientation q : ℝ)
    (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    (lapse*spinScale : ℂ)*rawPolynomial terms (growthSign sign*sourceWave .axialPhase q)
      ((orientation : ℂ)*(q : ℂ))/(growthSign sign*axialTimeDerivative q)=poleValue terms sign orientation q := by
  have wave : sourceWave .axialPhase q=(q : ℂ)*(Real.sqrt (axialRoot q) : ℂ) := by
    simp [sourceWave,sourcePower,axialRoot]
  have factor : growthSign sign*sourceWave .axialPhase q=
      (growthSign sign*(Real.sqrt (axialRoot q) : ℂ))*(q : ℂ) := by rw [wave]; ring
  rw [factor,polynomial_radial_factor,poleDenominator_source sign q small nonzero,poleValue]
  have qnonzero := Complex.ofReal_ne_zero.mpr nonzero
  have denominator := poleDenominator_nonzero sign q small
  field_simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
