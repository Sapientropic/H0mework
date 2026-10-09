import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Effect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem normalized_positive (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) (tau mu : ℝ)
    (positive : 0 < tau) (upper : ‖A‖ ≤ mu) : 0 ≤ normalizedAt tau mu A := by
  have lower := hermitian.isSelfAdjoint.neg_algebraMap_norm_le_self
  rw [Algebra.algebraMap_eq_smul_one] at lower
  have compare := smul_le_smul_of_nonneg_right upper (zero_le_one : (0 : Matrix ι ι ℂ) ≤ 1)
  have shifted : 0 ≤ mu • (1 : Matrix ι ι ℂ)+A := (neg_le_iff_add_nonneg').mp ((neg_le_neg compare).trans lower)
  have whole : 0 ≤ (tau+mu) • (1 : Matrix ι ι ℂ)+A := by
    have h := add_nonneg (smul_nonneg positive.le (zero_le_one : (0 : Matrix ι ι ℂ) ≤ 1)) shifted
    simpa only [add_smul,add_assoc] using h
  have den : 0 < tau+mu := by linarith [norm_nonneg A]
  have expression : normalizedAt tau mu A=(1/(2*(tau+mu)) : ℝ) • ((tau+mu) • (1 : Matrix ι ι ℂ)+A) := by
    ext i j
    simp only [normalizedAt,Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,Complex.real_smul]
    push_cast
    have complexDen : (tau : ℂ)+(mu : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt den
    field_simp [complexDen]
  rw [expression]
  exact smul_nonneg (by positivity) whole

omit [Fintype ι] in
theorem normalized_complement (A : Matrix ι ι ℂ) (tau mu : ℝ) :
    1-normalizedAt tau mu A=normalizedAt tau mu (-A) := by
  ext i j
  norm_num [normalizedAt,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.neg_apply]
  ring

theorem normalized_complement_positive (A : Matrix ι ι ℂ) (hermitian : A.IsHermitian) (tau mu : ℝ)
    (positive : 0 < tau) (upper : ‖A‖ ≤ mu) : 0 ≤ 1-normalizedAt tau mu A := by
  rw [normalized_complement]
  exact normalized_positive (-A) hermitian.neg tau mu positive (by simpa only [norm_neg] using upper)

theorem original_finite_effect_positive : 0 ≤ finiteEffect ∧ 0 ≤ 1-finiteEffect :=
  ⟨normalized_positive rationalCore rational_core_hermitian rationalRegularizer _ rational_regularizer_positive original_rational_norm_interval.2,
    normalized_complement_positive rationalCore rational_core_hermitian rationalRegularizer _ rational_regularizer_positive original_rational_norm_interval.2⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
