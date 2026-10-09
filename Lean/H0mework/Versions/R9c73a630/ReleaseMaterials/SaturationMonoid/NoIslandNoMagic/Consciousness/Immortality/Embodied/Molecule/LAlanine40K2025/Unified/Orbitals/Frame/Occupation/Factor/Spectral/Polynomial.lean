import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Physical

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section
attribute [local irreducible] Occupation.gamma Factor.projector24 Factor.normalizedFactor

private def Q : Matrix Basis Basis ℂ := (2 : ℂ) • projector24
private def E : Matrix Basis Basis ℂ := Occupation.gamma - Q

private theorem projector_norm_le_one : ‖projector24‖ ≤ 1 := by
  calc
    ‖projector24‖ = ‖normalizedFactor * normalizedFactor.conjTranspose‖ := by
      rw [projector24]
    _ ≤ ‖normalizedFactor‖ * ‖normalizedFactor.conjTranspose‖ :=
      Matrix.l2_opNorm_mul _ _
    _ = 1 := by rw [Matrix.l2_opNorm_conjTranspose,isometry_norm]; norm_num

private theorem Q_norm_le_two : ‖Q‖ ≤ 2 := by
  change ‖(2 : ℂ) • projector24‖ ≤ 2
  rw [norm_smul]
  have two : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [two]
  nlinarith [projector_norm_le_one]

private theorem gamma_norm_lt_four : ‖Occupation.gamma‖ < 4 := by
  have triangle : ‖Occupation.gamma‖ ≤ ‖E‖ + ‖Q‖ := by
    calc
      _ = ‖(Occupation.gamma - Q) + Q‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have residual : ‖E‖ < (1 / 10^5 : ℝ) := actual_U_gamma_projection_error
  linarith [Q_norm_le_two]

private theorem Q_quadratic : Q * Q = (2 : ℂ) • Q := by
  unfold Q
  rw [Matrix.smul_mul,Matrix.mul_smul,projector24_idempotent]

private theorem polynomial_identity :
    Occupation.gamma * Occupation.gamma - (2 : ℂ) • Occupation.gamma =
      Occupation.gamma * E + E * Q - (2 : ℂ) • E := by
  simp only [E, two_smul]
  have square : Q * Q = Q + Q := by simpa only [two_smul] using Q_quadratic
  noncomm_ring [square]

theorem actual_gamma_quadratic_gap :
    ‖Occupation.gamma * Occupation.gamma - (2 : ℂ) • Occupation.gamma‖ <
      (1 / 1000 : ℝ) := by
  have triangle :
      ‖Occupation.gamma * E + E * Q - (2 : ℂ) • E‖ ≤
        ‖Occupation.gamma‖ * ‖E‖ + ‖E‖ * ‖Q‖ + 2 * ‖E‖ := by
    have first := norm_add_le (Occupation.gamma * E) (E * Q)
    have second := norm_sub_le (Occupation.gamma * E + E * Q) ((2 : ℂ) • E)
    have a := norm_mul_le Occupation.gamma E
    have b := norm_mul_le E Q
    have c : ‖(2 : ℂ) • E‖ = 2 * ‖E‖ := by norm_num [norm_smul]
    nlinarith
  have residual : ‖E‖ < (1 / 10^5 : ℝ) := actual_U_gamma_projection_error
  rw [polynomial_identity]
  have enonnegative : 0 ≤ ‖E‖ := norm_nonneg _
  nlinarith [Q_norm_le_two,gamma_norm_lt_four]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
