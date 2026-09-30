import H0mework.Physics.LowEnergy.LightInteraction.Polynomial
import H0mework.Physics.LowEnergy.LightModes.MetricPole

/-! The original g00 source fixes both external pole residues. The opposite
leg has the opposite derivative orientation; no Hilbert adjoint is inserted. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
open LightModes Filter Topology
noncomputable section

def responseScale : ℝ := 9*Real.sqrt 15/6250

def sourceNumerator (z : ℂ) (q : ℝ) : ℂ :=
  -(4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
    sourcePolynomial (z^2) ((q : ℂ)^2)

def coupling (q : ℝ) : ℝ :=
  responseScale*currentNormal q/(axialRoot q*(axialDerivative q)^2)

theorem response_scale_positive : 0<responseScale := by
  unfold responseScale
  positivity

theorem coupling_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<coupling q := by
  exact div_pos (mul_pos response_scale_positive (current_normal_positive q small))
    (mul_pos (axial_root_positive q) (sq_pos_of_pos (axial_derivative_positive q small)))

theorem source_numerator_root (q : ℝ) :
    sourceNumerator (sourceWave .axialPhase q) q=
      -(4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
        ((q^2*currentNormal q : ℝ) : ℂ) := by
  unfold sourceNumerator
  rw [source_wave_square]
  simp only [sourcePower,pow_one]
  rw [Complex.ofReal_mul,Complex.ofReal_pow,source_polynomial_scaling]
  rw [show (q : ℂ)^2=((q^2 : ℝ) : ℂ) by norm_cast,complexValue_real]
  simp only [currentNormal,axialRoot,Complex.ofReal_mul,Complex.ofReal_add]

theorem source_squared_derivative (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    (squaredPolynomial .axialPhase (q^2)).derivative.eval (q^2*axialRoot q)=
      sourceCoefficient .axialPhase*axialDerivative q := by
  have domain := momentum_root_domain .axialPhase q small
  have source := source_root_simple .axialPhase (q^2) domain (pow_ne_zero _ nonzero)
  have generated := ((squaredPolynomial .axialPhase (q^2)).hasDerivAt (q^2*axialRoot q)).comp
    (axialRoot q) ((hasDerivAt_id (axialRoot q)).const_mul (q^2))
  simp only [squared_polynomial_eval,Function.comp_def,mul_one] at generated
  simp only [sourcePower,pow_one] at source
  have same := source.1.unique generated
  change sourceCoefficient .axialPhase*(q^2)*axialDerivative q=
    (squaredPolynomial .axialPhase (q^2)).derivative.eval (q^2*axialRoot q)*(q^2) at same
  apply mul_right_cancel₀ (pow_ne_zero 2 nonzero)
  calc
    _ = sourceCoefficient .axialPhase*(q^2)*axialDerivative q := same.symm
    _ = _ := by ring

theorem source_time_derivative (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    axialTimeDerivative q=
      (sourceCoefficient .axialPhase : ℂ)*(axialDerivative q : ℂ)*(2*sourceWave .axialPhase q) := by
  unfold axialTimeDerivative
  congr 1
  rw [source_wave_square,complexSquaredPolynomial,Polynomial.derivative_map]
  simp only [sourcePower,pow_one]
  change ((squaredPolynomial .axialPhase (q^2)).derivative.map Complex.ofRealHom).eval
    (Complex.ofRealHom (q^2*axialRoot q))=_
  rw [Polynomial.eval_map_apply,source_squared_derivative q small nonzero]
  simp

theorem source_time_derivative_squared (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    (axialTimeDerivative q)^2=
      4*(sourceCoefficient .axialPhase : ℂ)^2*
        ((q^2*axialRoot q*(axialDerivative q)^2 : ℝ) : ℂ) := by
  rw [source_time_derivative q small nonzero]
  simp only [mul_pow,source_wave_square,sourcePower,pow_one]
  push_cast
  unfold axialRoot
  ring

theorem original_double_residue (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    sourceNumerator (sourceWave .axialPhase q) q/(axialTimeDerivative q)^2= -(coupling q : ℂ) := by
  rw [source_numerator_root,source_time_derivative_squared q small nonzero]
  have hn : (q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have hc : (sourceCoefficient .axialPhase : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (source_coefficient_nonzero .axialPhase)
  have hr : (axialRoot q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (axial_root_positive q).ne'
  have hd : (axialDerivative q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (axial_derivative_positive q small).ne'
  unfold coupling
  push_cast
  field_simp [hn,hc,hr,hd]

theorem coupling_limit : Tendsto coupling (𝓝 0) (𝓝 responseScale) := by
  have denom := axial_root_limit.mul (axial_derivative_limit.pow 2)
  have generated := (current_normal_limit.const_mul responseScale).div denom (by norm_num)
  convert! generated using 1
  simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
