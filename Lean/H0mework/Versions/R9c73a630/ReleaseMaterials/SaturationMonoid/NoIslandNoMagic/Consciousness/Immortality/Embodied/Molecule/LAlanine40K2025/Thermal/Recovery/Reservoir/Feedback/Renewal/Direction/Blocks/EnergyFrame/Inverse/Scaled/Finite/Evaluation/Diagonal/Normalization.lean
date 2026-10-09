import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Values

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

def gibbsMass : ℚ := ∑ i : Basis, (gibbsValue i).1

theorem gibbs_values_positive : ∀ i : Basis, 0 < (gibbsValue i).1 ∧ (gibbsValue i).2=0 := by decide +kernel

theorem gibbs_mass_lower : (60000000 : ℚ) ≤ gibbsMass := by decide +kernel

def computedGibbs : Matrix Basis Basis ℂ := Matrix.diagonal (fun i => (((gibbsValue i).1/gibbsMass : ℚ) : ℂ))

theorem gibbs_mass_positive : 0 < gibbsMass := lt_of_lt_of_le (by norm_num : (0 : ℚ) < 60000000) gibbs_mass_lower

theorem gibbs_matrix_diagonal : gibbsMatrix=Matrix.diagonal (fun i => ((gibbsValue i).1 : ℂ)) := by
  ext i j
  simp [gibbsMatrix,Scalar.value,(gibbs_values_positive _).2]

theorem gibbs_matrix_trace : gibbsMatrix.trace=(gibbsMass : ℂ) := by
  rw [gibbs_matrix_diagonal,Matrix.trace_diagonal]
  simp only [gibbsMass,Rat.cast_sum]

theorem computed_gibbs_positive : computedGibbs.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  have valuePositive : (0 : ℚ) ≤ (gibbsValue i).1/gibbsMass :=
    div_nonneg (gibbs_values_positive i).1.le gibbs_mass_positive.le
  change (0 : ℂ) ≤ (((gibbsValue i).1/gibbsMass : ℚ) : ℂ)
  apply Complex.nonneg_iff.mpr
  constructor
  · have realPositive := rational_order valuePositive
    simpa only [Complex.ratCast_re,Rat.cast_zero] using realPositive
  · simp

theorem computed_gibbs_trace : computedGibbs.trace=1 := by
  have weights : (∑ i : Basis, (gibbsValue i).1/gibbsMass)=1 := by
    rw [← Finset.sum_div]
    change gibbsMass/gibbsMass=1
    exact div_self gibbs_mass_positive.ne'
  rw [computedGibbs,Matrix.trace_diagonal,← Rat.cast_sum,weights]
  norm_num

theorem computed_gibbs_normalization : gibbsMatrix.trace⁻¹ • gibbsMatrix=computedGibbs := by
  rw [gibbs_matrix_trace,gibbs_matrix_diagonal]
  ext i j
  by_cases same : i=j
  · subst j
    simp [computedGibbs,Matrix.smul_apply,div_eq_mul_inv,mul_comm]
  · simp [computedGibbs,Matrix.smul_apply,same]

theorem original_computed_gibbs_error : ‖Input.finiteGibbs-computedGibbs‖ ≤ (5/10^18 : ℝ) := by
  have mass : (60000000 : ℝ) ≤ ‖gibbsMatrix.trace‖ := by
    rw [gibbs_matrix_trace,Complex.norm_ratCast]
    have lower := rational_order gibbs_mass_lower
    have positive : (0 : ℝ) ≤ (gibbsMass : ℝ) := by simpa only [Rat.cast_zero] using rational_order gibbs_mass_positive.le
    rw [abs_of_nonneg positive]
    exact_mod_cast lower
  have reference : ‖gibbsMatrix.trace⁻¹ • gibbsMatrix‖ ≤ 1 := by
    rw [computed_gibbs_normalization]
    exact Input.state_norm_le_one _ computed_gibbs_positive computed_gibbs_trace
  have bound := Input.trace_normalization_error Input.gibbsNumeratorPolynomial gibbsMatrix
    60000000 (3/10^12) (by norm_num) (by norm_num [Basis]) mass reference actual_gibbs_matrix_error
  rw [computed_gibbs_normalization] at bound
  exact bound.trans (by norm_num [Basis])

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
