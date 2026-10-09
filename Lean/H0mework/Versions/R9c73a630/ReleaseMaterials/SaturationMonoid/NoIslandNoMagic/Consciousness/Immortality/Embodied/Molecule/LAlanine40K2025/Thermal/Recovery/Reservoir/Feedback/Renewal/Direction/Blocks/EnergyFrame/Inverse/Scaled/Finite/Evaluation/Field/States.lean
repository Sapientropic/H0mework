import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Errors
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Net

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedSystemWord : Matrix Basis Basis ℂ := computedPolynomial*Diagonal.activeMatrix
def computedSystem : Matrix Basis Basis ℂ := computedSystemWord*Dense.computedBase*star computedSystemWord
def computedBath : Matrix Basis Basis ℂ := computedPolynomial*Diagonal.computedGibbs*star computedPolynomial

theorem computed_polynomial_norm : ‖computedPolynomial‖ ≤ 3 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub computedPolynomial Input.fieldPolynomial 0
  simp only [sub_zero] at triangle
  have paid := field_numeric_error
  rw [norm_sub_rev] at paid
  linarith [Diagonal.field_polynomial_norm]

theorem actual_active_norm : ‖Diagonal.activeMatrix‖ ≤ 2 := by
  rw [Diagonal.activeMatrix,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  have bound := Diagonal.rational_norm_from_square (Diagonal.activeValue i) 2 (by norm_num)
    (by simpa only [Diagonal.activeValue,show (2 : ℚ)^2=4 by norm_num] using (Diagonal.activeMaterial i).stageNorm 10)
  exact bound

theorem system_word_error : ‖Diagonal.computedSystemWord-computedSystemWord‖ ≤ (1/10^17 : ℝ) := by
  change ‖Input.fieldPolynomial*Diagonal.activeMatrix-computedPolynomial*Diagonal.activeMatrix‖ ≤ _
  rw [← Matrix.sub_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul field_numeric_error actual_active_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem computed_system_word_norm : ‖computedSystemWord‖ ≤ 4 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub computedSystemWord Diagonal.computedSystemWord 0
  simp only [sub_zero] at triangle
  have paid := system_word_error
  rw [norm_sub_rev] at paid
  linarith [Diagonal.computed_system_word_norm]

theorem system_numeric_error : ‖Diagonal.computedSystem-computedSystem‖ ≤ (2/10^16 : ℝ) := by
  have paid := Post.raw_sandwich_change (star Diagonal.computedSystemWord) (star computedSystemWord) Input.rawBaseSystem
  simp only [star_star,norm_star,← star_sub] at paid
  rw [computedSystem,← Dense.original_base_exact]
  apply paid.trans
  exact (mul_le_mul (mul_le_mul (add_le_add Diagonal.computed_system_word_norm computed_system_word_norm)
    Diagonal.raw_base_norm (norm_nonneg _) (by norm_num)) system_word_error (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem bath_numeric_error : ‖Diagonal.computedBath-computedBath‖ ≤ (3/10^17 : ℝ) := by
  have normBound := Input.state_norm_le_one Diagonal.computedGibbs Diagonal.computed_gibbs_positive Diagonal.computed_gibbs_trace
  have paid := Post.raw_sandwich_change (star Input.fieldPolynomial) (star computedPolynomial) Diagonal.computedGibbs
  simp only [star_star,norm_star,← star_sub] at paid
  exact paid.trans ((mul_le_mul (mul_le_mul (add_le_add Diagonal.field_polynomial_norm computed_polynomial_norm)
    normBound (norm_nonneg _) (by norm_num)) field_numeric_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem computed_system_norm : ‖computedSystem‖ ≤ 3 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub computedSystem Diagonal.computedSystem 0
  simp only [sub_zero] at triangle
  have paid := system_numeric_error
  rw [norm_sub_rev] at paid
  linarith [Diagonal.computed_system_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
