import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalPC

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Propagation.Producer Load.Source
open scoped Matrix Matrix.Norms.L2Operator

abbrev DiagonalMaterial (a : Basis) := ∀ n : Fin 2, ScalarMaterial (diagonalScalarEnergy a n)

noncomputable def diagonalMaterialOne (a : Basis) (M : DiagonalMaterial a) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun n => Scalar.value (M n).one)

noncomputable def diagonalMaterialTwo (a : Basis) (M : DiagonalMaterial a) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun n => Scalar.value (M n).two)

theorem diagonal_material_one_error (a : Basis) (M : DiagonalMaterial a) :
    ‖Phase.pcPolynomial.submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))-diagonalMaterialOne a M‖ ≤ (1/10^24 : ℝ) := by
  rw [Phase.pcPolynomial,diagonal_pc_original]
  have formula := diagonal_pc_scalar_values a 1
  norm_num only [Rat.cast_one,one_mul] at formula
  rw [formula,diagonalMaterialOne,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro n
  exact material_one_error _ (M n)

theorem diagonal_material_two_error (a : Basis) (M : DiagonalMaterial a) :
    ‖Actions.parentPCPolynomial.submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))-diagonalMaterialTwo a M‖ ≤ (1/10^24 : ℝ) := by
  rw [Actions.parentPCPolynomial,diagonal_pc_original]
  have formula := diagonal_pc_scalar_values a 2
  norm_num only [Rat.cast_ofNat] at formula
  rw [formula,diagonalMaterialTwo,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro n
  exact material_two_error _ (M n)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
