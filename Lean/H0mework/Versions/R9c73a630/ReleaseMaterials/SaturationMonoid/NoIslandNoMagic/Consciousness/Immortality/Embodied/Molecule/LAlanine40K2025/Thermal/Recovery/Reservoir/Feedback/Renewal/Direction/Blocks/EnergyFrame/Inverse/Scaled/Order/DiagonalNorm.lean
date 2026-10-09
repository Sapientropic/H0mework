import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.DiagonalCore

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def diagonalNormBound : ℝ := max ‖rationalCore.submatrix (diagonalPCE 0) (diagonalPCE 0)‖
  ‖rationalCore.submatrix (diagonalPCE 96) (diagonalPCE 96)‖
def donorNorm : ℝ := ‖rationalCore.submatrix (diagonalPCE 97) (diagonalPCE 97)‖
def wholeNormBound : ℝ := max offDiagonalNormBound (max diagonalNormBound donorNorm)

theorem ordinary_diagonal_norm (a : Fin 97) :
    ‖rationalCore.submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)‖ ≤ diagonalNormBound := by
  have bounds := original_diagonal_envelope a
  exact norm_of_envelope _ _ _ (rational_core_hermitian.submatrix _) (rational_core_hermitian.submatrix _)
    (rational_core_hermitian.submatrix _) bounds.1 bounds.2

theorem all_diagonal_norm (a : Basis) :
    ‖rationalCore.submatrix (diagonalPCE a) (diagonalPCE a)‖ ≤ max diagonalNormBound donorNorm := by
  by_cases top : a=(97 : Basis)
  · subst a
    exact le_max_right _ _
  · have inside : a.val < 97 := by
      have av := a.isLt
      have different : a.val ≠ 97 := fun same => top (Fin.ext same)
      omega
    have same : (⟨a.val,inside⟩ : Fin 97).castSucc=a := Fin.ext rfl
    rw [← same]
    exact (ordinary_diagonal_norm ⟨a.val,inside⟩).trans (le_max_left _ _)

theorem whole_bound_nonnegative : 0 ≤ wholeNormBound := by
  exact (norm_nonneg (rationalCore.submatrix (orbitPCE 0 1) (orbitPCE 0 1))).trans
    ((le_max_left _ _).trans (le_max_left _ _))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
