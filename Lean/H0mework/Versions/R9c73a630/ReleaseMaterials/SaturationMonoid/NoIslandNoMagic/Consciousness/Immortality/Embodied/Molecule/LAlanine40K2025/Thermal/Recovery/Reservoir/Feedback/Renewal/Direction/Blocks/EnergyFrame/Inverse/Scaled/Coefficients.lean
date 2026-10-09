import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.FiniteGain

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem scaled_inverse (c s : ℝ) (nonzero : c ≠ 0) (circle : c^2+s^2=1) :
    (c : ℂ)^2*((c : ℂ)^2+Complex.I*c*s)⁻¹=(c : ℂ)^2-Complex.I*c*s := by
  have denominator : (c : ℂ)^2+Complex.I*c*s ≠ 0 := by
    intro zero
    have realPart := congrArg Complex.re zero
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.zero_re,zero_mul,mul_zero,sub_zero,add_zero,pow_two] at realPart
    exact nonzero ((mul_self_eq_zero.mp realPart))
  have castCircle : (c : ℂ)^2+(s : ℂ)^2=1 := by exact_mod_cast circle
  have product : ((c : ℂ)^2-Complex.I*c*s)*((c : ℂ)^2+Complex.I*c*s)=(c : ℂ)^2 := by
    have isq := Complex.I_sq
    calc
      _ = (c : ℂ)^4-Complex.I^2*(c : ℂ)^2*(s : ℂ)^2 := by ring
      _ = (c : ℂ)^2*((c : ℂ)^2+(s : ℂ)^2) := by rw [isq]; ring
      _ = _ := by rw [castCircle,mul_one]
  calc
    _ = (((c : ℂ)^2-Complex.I*c*s)*((c : ℂ)^2+Complex.I*c*s))*((c : ℂ)^2+Complex.I*c*s)⁻¹ := congrArg (fun z : ℂ => z*((c : ℂ)^2+Complex.I*c*s)⁻¹) product.symm
    _ = _ := by rw [mul_assoc,mul_inv_cancel₀ denominator,mul_one]

theorem plus_scaled : (Real.cos BasisInverse.actualAngle : ℂ)^2*plusCoefficient=
    -(Real.sin BasisInverse.actualAngle : ℂ)^2-Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle := by
  have nonzero : Real.cos BasisInverse.actualAngle ≠ 0 := by linarith [source_cos_lower]
  have castNonzero : (Real.cos BasisInverse.actualAngle : ℂ)^2 ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr nonzero)
  unfold plusCoefficient
  rw [mul_sub,scaled_inverse _ _ nonzero (Real.cos_sq_add_sin_sq _),mul_inv_cancel₀ castNonzero]
  have circle : (Real.cos BasisInverse.actualAngle : ℂ)^2+(Real.sin BasisInverse.actualAngle : ℂ)^2=1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq BasisInverse.actualAngle
  linear_combination circle

theorem minus_scaled : (Real.cos BasisInverse.actualAngle : ℂ)^2*minusCoefficient=
    -(Real.sin BasisInverse.actualAngle : ℂ)^2+Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle := by
  have paid := congrArg star plus_scaled
  simp only [star_mul,star_pow,star_sub,star_neg,coefficients_star] at paid
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.conj_I] at paid
  linear_combination paid

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
