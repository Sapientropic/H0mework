import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Diagonal

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def pairIndex : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv

theorem diagonal_index_injective (a : Basis) : Function.Injective (diagonalPCE a) := by
  intro i j same
  apply (diagonalPCEEquiv a).injective
  exact Subtype.ext same

def diagonalEffect (a : Fin 97) (sign : ℚ) : Matrix (Fin 4) (Fin 4) ℂ :=
  cast (effectReal (diagonal a) sign) (effectImag (0 : Matrix (Fin 4) (Fin 4) ℚ) sign)

theorem diagonal_effect_source (a : Fin 97) : finiteEffect.submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)=
    (diagonalEffect a 1).submatrix pairIndex pairIndex := by
  rw [finiteEffect,normalized_submatrix _ (diagonal_index_injective _),diagonal_source a]
  rw [← normalized_submatrix (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) finProdFinEquiv.injective]
  simp only [diagonalEffect,effect_cast,Rat.cast_one,one_smul,pairIndex]

theorem diagonal_complement_source (a : Fin 97) : (1-finiteEffect).submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)=
    (diagonalEffect a (-1)).submatrix pairIndex pairIndex := by
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ (diagonal_index_injective _),diagonal_effect_source a]
  have same : diagonalEffect a (-1)=1-diagonalEffect a 1 := by
    simp only [diagonalEffect,effect_cast,Rat.cast_one,Rat.cast_neg,one_smul,neg_one_smul,normalized_complement]
  rw [same]
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ pairIndex.injective]

theorem diagonal_positive (a : Fin 97) : 0 ≤ diagonalEffect a 1 ∧ 0 ≤ diagonalEffect a (-1) := by
  have up := (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1).submatrix (diagonalPCE a.castSucc)
  have down := (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2).submatrix (diagonalPCE a.castSucc)
  rw [diagonal_effect_source a] at up
  rw [diagonal_complement_source a] at down
  have undo (M : Matrix (Fin 4) (Fin 4) ℂ) : (M.submatrix pairIndex pairIndex).submatrix pairIndex.symm pairIndex.symm=M := by
    ext i j
    change M (pairIndex (pairIndex.symm i)) (pairIndex (pairIndex.symm j))=M i j
    simp only [Equiv.apply_symm_apply]
  have u := up.submatrix pairIndex.symm
  have d := down.submatrix pairIndex.symm
  rw [undo] at u d
  exact ⟨u.nonneg,d.nonneg⟩

theorem original_diagonal_root_restriction (a : Basis) :
    (CFC.sqrt finiteEffect).submatrix (diagonalPCE a) (diagonalPCE a)=
      CFC.sqrt (finiteEffect.submatrix (diagonalPCE a) (diagonalPCE a)) := by
  have positive := Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1
  have same := restrict_sqrt finite_effect_preserves positive s(a,a)
  have renamed := congrArg (fun M => M.submatrix (diagonalPCEEquiv a) (diagonalPCEEquiv a)) same
  rw [reindex_sqrt (diagonalPCEEquiv a) (restrict pceOrbit s(a,a) finiteEffect) (positive.submatrix Subtype.val)] at renamed
  exact renamed

theorem original_diagonal_complement_restriction (a : Basis) :
    (CFC.sqrt (1-finiteEffect)).submatrix (diagonalPCE a) (diagonalPCE a)=
      CFC.sqrt ((1-finiteEffect).submatrix (diagonalPCE a) (diagonalPCE a)) := by
  have positive := Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2
  have same := restrict_sqrt (preserves_sub (preserves_one pceOrbit) finite_effect_preserves) positive s(a,a)
  have renamed := congrArg (fun M => M.submatrix (diagonalPCEEquiv a) (diagonalPCEEquiv a)) same
  rw [reindex_sqrt (diagonalPCEEquiv a) (restrict pceOrbit s(a,a) (1-finiteEffect)) (positive.submatrix Subtype.val)] at renamed
  exact renamed

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
