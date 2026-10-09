import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ReverseFlow
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Collision Propagation.Interface Load.Source Powered.Source Powered.Dynamics Propagation.Producer
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem diagonal_interaction_zero (a : Basis) :
    (interaction E).submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))=0 := by
  rw [Scaled.Order.source_E_diagonal]
  ext c d
  simp only [Matrix.submatrix_apply,interaction,transfer,Matrix.add_apply,Matrix.conjTranspose_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,raising_entry]
  simp

theorem diagonal_reverse_hamiltonian (a : Basis) :
    (Actions.reversePCH E).submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))=
      diagonalHpc (Donor.calculatedEnergy a) := by
  have split : Actions.reversePCH E=sourcePCH E-(2 : ℂ) • interaction E := by
    unfold Actions.reversePCH sourcePCH totalHamiltonian
    module
  rw [split,Matrix.submatrix_sub,Matrix.submatrix_smul]
  simp only [Pi.sub_apply,Pi.smul_apply]
  rw [Scaled.Order.numeric_diagonal_PC a,diagonal_interaction_zero,smul_zero,sub_zero]

theorem diagonal_recovery_original (a : Basis) :
    Actions.recoveryPCPolynomial.submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))=
      diagonalPC a (3*(nativeClockStep : ℝ)) := by
  have kept : Preserves pcOrbit (Actions.reversePCH E) := Contraction.diagonal_reverse_preserves _
  have restricted := original_flow_restriction kept s(a,a) (diagonalEquiv a) (3*(nativeClockStep : ℝ))
  have source : ((restrict pcOrbit s(a,a) (Actions.reversePCH E)).submatrix (diagonalEquiv a) (diagonalEquiv a))=
      diagonalHpc (Donor.calculatedEnergy a) := diagonal_reverse_hamiltonian a
  rw [source] at restricted
  exact restricted

def diagonalMaterialThree (a : Basis) (M : DiagonalMaterial a) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun n => Scalar.value (M n).three)

theorem diagonal_material_three_error (a : Basis) (M : DiagonalMaterial a) :
    ‖Actions.recoveryPCPolynomial.submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))-diagonalMaterialThree a M‖ ≤ (1/10^24 : ℝ) := by
  rw [diagonal_recovery_original]
  have formula := diagonal_pc_scalar_values a 3
  norm_num only [Rat.cast_ofNat] at formula
  rw [formula,diagonalMaterialThree,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro n
  exact material_three_error _ (M n)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
