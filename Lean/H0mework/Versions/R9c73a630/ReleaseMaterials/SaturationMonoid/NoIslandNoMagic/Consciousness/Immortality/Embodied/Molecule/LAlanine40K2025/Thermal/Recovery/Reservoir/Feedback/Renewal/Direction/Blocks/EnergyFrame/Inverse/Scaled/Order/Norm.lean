import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Core

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_of_envelope (A L U : Matrix ι ι ℂ) (ha : A.IsHermitian) (hl : L.IsHermitian) (hu : U.IsHermitian)
    (lower : L ≤ A) (upper : A ≤ U) : ‖A‖ ≤ max ‖L‖ ‖U‖ := by
  apply self_adjoint_norm_of_sides _ ha _ (le_max_of_le_left (norm_nonneg L))
  · have top := hu.isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at top
    exact upper.trans (top.trans (smul_le_smul_of_nonneg_right (le_max_right _ _) zero_le_one))
  · have bottom := hl.isSelfAdjoint.neg_algebraMap_norm_le_self
    rw [Algebra.algebraMap_eq_smul_one,← neg_smul] at bottom
    exact (smul_le_smul_of_nonneg_right (neg_le_neg (le_max_left _ _)) zero_le_one).trans (bottom.trans lower)

def offDiagonalNormBound : ℝ := max
  ‖rationalCore.submatrix (orbitPCE 0 1) (orbitPCE 0 1)‖
  ‖rationalCore.submatrix (orbitPCE 96 97) (orbitPCE 96 97)‖

theorem all_offDiagonal_norm (a b : Basis) (ordered : a < b) :
    ‖rationalCore.submatrix (orbitPCE a b) (orbitPCE a b)‖ ≤ offDiagonalNormBound := by
  have bounds := original_rational_offDiagonal_envelope a b ordered
  exact norm_of_envelope _ _ _ (rational_core_hermitian.submatrix _) (rational_core_hermitian.submatrix _)
    (rational_core_hermitian.submatrix _) bounds.1 bounds.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
