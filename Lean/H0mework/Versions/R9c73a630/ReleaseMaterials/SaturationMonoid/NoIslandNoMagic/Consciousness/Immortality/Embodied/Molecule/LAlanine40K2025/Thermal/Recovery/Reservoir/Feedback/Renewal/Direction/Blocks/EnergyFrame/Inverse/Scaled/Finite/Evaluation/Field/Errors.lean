import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.ResidualNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term1.Steps
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term2.Steps
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term3.Steps
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term4.Steps
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term5.Steps
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term6.Steps
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field.Term7.Steps

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator

theorem all_steps (n : Nat) (bound : n < 7) (j : Basis) :
    Check n (Rows.rowAt (termColumns n) j) (Rows.rowAt (termColumns (n+1)) j) := by
  interval_cases n
  · rw [term_zero_column]; exact term1_all_steps j
  · exact term2_all_steps j
  · exact term3_all_steps j
  · exact term4_all_steps j
  · exact term5_all_steps j
  · exact term6_all_steps j
  · exact term7_all_steps j

theorem integer_residual_bound (n : Nat) (bound : n < 7) (i j : Basis) :
    |clockNumerator*(Dense.fieldInt*termInt n) i j-stepDenominator n*termInt (n+1) i j| ≤ stepDenominator n := by
  have checked := checked_entry n (Rows.rowAt (termColumns n) j) (Rows.rowAt (termColumns (n+1)) j)
    (term_column_lengths (n+1) (by omega) j) (all_steps n bound j) i
  have product : Rows.dot (Rows.rowAt Dense.fieldRows i) (Rows.rowAt (termColumns n) j)=
      (Dense.fieldInt*termInt n) i j :=
    Rows.dot_eq_sum _ _ (Dense.fieldRows_lengths i) (term_column_lengths n (by omega) j)
  rw [product] at checked
  exact checked

noncomputable section

theorem source_step_error (n : Nat) (bound : n < 7) :
    ‖termMatrix (n+1)-(((n+1 : Nat) : ℂ)⁻¹) • (K*termMatrix n)‖ ≤ (1/10^22 : ℝ) := by
  rw [source_step_representation,termMatrix]
  exact integer_matrix_residual Dense.fieldInt (termInt n) (termInt (n+1)) clockNumerator
    (stepDenominator n) (step_denominator_positive n) (integer_residual_bound n bound)

theorem original_term_error (n : Nat) (bound : n < 8) : ‖realTerm K n-termMatrix n‖ ≤ (2/10^22 : ℝ) :=
  rounded_terms_error K termMatrix K_norm termMatrix_zero source_step_error n (by omega)

def computedPolynomial : Matrix Basis Basis ℂ := phasedSum termMatrix 8

theorem field_numeric_error : ‖Input.fieldPolynomial-computedPolynomial‖ ≤ (5/10^18 : ℝ) := by
  rw [original_polynomial_argument]
  have first := short_polynomial_truncation (-Complex.I • K) source_argument_norm
  have second := rounded_phased_sum_error K termMatrix original_term_error
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Phase.polynomial (-Complex.I • K) 14)
    (Phase.polynomial (-Complex.I • K) 8) computedPolynomial
  change ‖Phase.polynomial (-Complex.I • K) 8-computedPolynomial‖ ≤ _ at second
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Field
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
