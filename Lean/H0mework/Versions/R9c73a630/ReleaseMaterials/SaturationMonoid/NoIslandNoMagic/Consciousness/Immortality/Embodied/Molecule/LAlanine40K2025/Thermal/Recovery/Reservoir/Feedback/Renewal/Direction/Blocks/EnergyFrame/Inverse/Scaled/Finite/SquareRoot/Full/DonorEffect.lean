import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.DiagonalEffect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def donorEffect (sign : ℚ) : Matrix (Fin 4) (Fin 4) ℂ := cast (effectReal real4 sign) (effectImag imag4 sign)

theorem donor_effect_source : finiteEffect.submatrix (diagonalPCE 97) (diagonalPCE 97)=
    (donorEffect 1).submatrix pairIndex pairIndex := by
  rw [finiteEffect,normalized_submatrix _ (diagonal_index_injective _),source_donor_core,source_block4]
  rw [← normalized_submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) finProdFinEquiv.injective]
  simp only [donorEffect,effect_cast,Rat.cast_one,one_smul,rational_block4,pairIndex]

theorem donor_complement_source : (1-finiteEffect).submatrix (diagonalPCE 97) (diagonalPCE 97)=
    (donorEffect (-1)).submatrix pairIndex pairIndex := by
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ (diagonal_index_injective _),donor_effect_source]
  have same : donorEffect (-1)=1-donorEffect 1 := by
    simp only [donorEffect,effect_cast,Rat.cast_one,Rat.cast_neg,one_smul,neg_one_smul,normalized_complement]
  rw [same]
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ pairIndex.injective]

theorem donor_positive : 0 ≤ donorEffect 1 ∧ 0 ≤ donorEffect (-1) := by
  have up := (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1).submatrix (diagonalPCE 97)
  have down := (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2).submatrix (diagonalPCE 97)
  rw [donor_effect_source] at up
  rw [donor_complement_source] at down
  have undo (M : Matrix (Fin 4) (Fin 4) ℂ) : (M.submatrix pairIndex pairIndex).submatrix pairIndex.symm pairIndex.symm=M := by
    ext i j
    change M (pairIndex (pairIndex.symm i)) (pairIndex (pairIndex.symm j))=M i j
    simp only [Equiv.apply_symm_apply]
  have u := up.submatrix pairIndex.symm
  have d := down.submatrix pairIndex.symm
  rw [undo] at u d
  exact ⟨u.nonneg,d.nonneg⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
