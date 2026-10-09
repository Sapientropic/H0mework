import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Clock

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem off_diagonal_inverse_bound (sign : ℝ) :
    ‖((Real.cos BasisInverse.actualAngle : ℂ)^2+
      (sign : ℂ)*Complex.I*Real.cos BasisInverse.actualAngle*Real.sin BasisInverse.actualAngle)⁻¹‖ ≤ 6000000 := by
  let c := Real.cos BasisInverse.actualAngle
  let s := Real.sin BasisInverse.actualAngle
  let z := (c : ℂ)^2+(sign : ℂ)*Complex.I*c*s
  have lower : c^2 ≤ ‖z‖ := by
    have h := Complex.re_le_norm z
    dsimp only [z] at h
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,pow_two] at h
    simpa only [z,pow_two] using h
  have cp : 0 < c := by dsimp only [c]; linarith [source_cos_lower]
  have normPositive : 0 < ‖z‖ := (sq_pos_of_pos cp).trans_le lower
  change ‖z⁻¹‖ ≤ _
  rw [norm_inv,inv_eq_one_div]
  apply (div_le_iff₀ normPositive).mpr
  dsimp only [c] at lower
  nlinarith [source_cos_lower]

theorem plus_coefficient_bound : ‖plusCoefficient‖ ≤ 12000000 := by
  have h := off_diagonal_inverse_bound 1
  simp only [Complex.ofReal_one,one_mul] at h
  exact (norm_sub_le _ _).trans (by linarith [source_cos_inverse_square])

theorem minus_coefficient_bound : ‖minusCoefficient‖ ≤ 12000000 := by
  have h := off_diagonal_inverse_bound (-1)
  simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul,← sub_eq_add_neg] at h
  exact (norm_sub_le _ _).trans (by linarith [source_cos_inverse_square])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
