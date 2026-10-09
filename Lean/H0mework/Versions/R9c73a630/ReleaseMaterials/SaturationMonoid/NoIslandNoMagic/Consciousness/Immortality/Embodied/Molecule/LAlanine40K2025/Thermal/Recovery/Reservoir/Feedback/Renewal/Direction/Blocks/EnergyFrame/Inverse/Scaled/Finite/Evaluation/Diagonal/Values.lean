import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Matrices
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Errors
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.ActiveRows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.GibbsRows

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

def activeValue (i : Basis) : Scalar.QComplex := (activeMaterial i).rows 10
def gibbsValue (i : Basis) : Scalar.QComplex := (gibbsMaterial i).rows 7

def activeMatrix : Matrix Basis Basis ℂ := Matrix.diagonal (fun i => Scalar.value (activeValue i))
def gibbsMatrix : Matrix Basis Basis ℂ := Matrix.diagonal (fun i => Scalar.value (gibbsValue i))

theorem actual_active_values_error : ∀ i : Basis, ‖(activeInitial i)^1024-Scalar.value (activeValue i)‖ ≤ (2/10^18 : ℝ) :=
  fun i => active_final_error i (activeMaterial i)

theorem actual_gibbs_values_error : ∀ i : Basis, ‖(gibbsInitial i)^128-Scalar.value (gibbsValue i)‖ ≤ (3/10^12 : ℝ) :=
  fun i => gibbs_final_error i (gibbsMaterial i)

theorem actual_active_matrix_error : ‖Input.activePolynomial-activeMatrix‖ ≤ (2/10^18 : ℝ) := by
  rw [original_active_matrix]
  exact diagonal_distance _ _ _ (by norm_num) actual_active_values_error

theorem actual_gibbs_matrix_error : ‖Input.gibbsNumeratorPolynomial-gibbsMatrix‖ ≤ (3/10^12 : ℝ) := by
  rw [original_gibbs_numerator]
  exact diagonal_distance _ _ _ (by norm_num) actual_gibbs_values_error

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
