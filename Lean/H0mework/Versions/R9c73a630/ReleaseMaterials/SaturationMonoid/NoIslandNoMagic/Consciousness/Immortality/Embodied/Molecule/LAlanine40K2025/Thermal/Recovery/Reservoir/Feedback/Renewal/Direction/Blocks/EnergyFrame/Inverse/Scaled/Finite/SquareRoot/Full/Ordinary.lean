import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Model
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.FirstConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def ordinary (a b : Basis) : Matrix (Fin 8) (Fin 8) ℚ := expandedRational (energy a) (energy b) (sine^2) donorEnergy

theorem ordinary_source (a b : Basis) (distinct : a ≠ b) :
    rationalCore.submatrix (orbitPCE a b) (orbitPCE a b)=(cast (ordinary a b) 0).submatrix tripleIndex tripleIndex := by
  rw [original_rational_block a b distinct,ordinary_expanded]
  have same := expanded_cast (energy a) (energy b) (sine^2) donorEnergy
  simp only [energy_cast,Rat.cast_pow,sine_cast,donor_cast] at same
  rw [← same]
  rfl

theorem index_injective (a b : Basis) (distinct : a ≠ b) : Function.Injective (orbitPCE a b) := by
  intro i j same
  apply (offDiagonalPCEEquiv a b distinct).injective
  exact Subtype.ext same

def ordinaryEffect (a b : Basis) (sign : ℚ) : Matrix (Fin 8) (Fin 8) ℂ :=
  cast (effectReal (ordinary a b) sign) (effectImag (0 : Matrix (Fin 8) (Fin 8) ℚ) sign)

theorem ordinary_effect_source (a b : Basis) (distinct : a ≠ b) :
    finiteEffect.submatrix (orbitPCE a b) (orbitPCE a b)=(ordinaryEffect a b 1).submatrix tripleIndex tripleIndex := by
  rw [finiteEffect,normalized_submatrix _ (index_injective a b distinct),ordinary_source a b distinct]
  rw [← normalized_submatrix tripleIndex tripleIndex.injective]
  simp only [ordinaryEffect,effect_cast,Rat.cast_one,one_smul]

theorem ordinary_complement_source (a b : Basis) (distinct : a ≠ b) :
    (1-finiteEffect).submatrix (orbitPCE a b) (orbitPCE a b)=(ordinaryEffect a b (-1)).submatrix tripleIndex tripleIndex := by
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ (index_injective a b distinct),ordinary_effect_source a b distinct]
  have same : ordinaryEffect a b (-1)=1-ordinaryEffect a b 1 := by
    simp only [ordinaryEffect,effect_cast,Rat.cast_one,Rat.cast_neg,one_smul,neg_one_smul,normalized_complement]
  rw [same]
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ tripleIndex.injective]

theorem ordinary_positive (a b : Basis) (distinct : a ≠ b) :
    0 ≤ ordinaryEffect a b 1 ∧ 0 ≤ ordinaryEffect a b (-1) := by
  have up := (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.1).submatrix (orbitPCE a b)
  have down := (Matrix.nonneg_iff_posSemidef.mp original_finite_effect_positive.2).submatrix (orbitPCE a b)
  rw [ordinary_effect_source a b distinct] at up
  rw [ordinary_complement_source a b distinct] at down
  have upFull := up.submatrix tripleIndex.symm
  have downFull := down.submatrix tripleIndex.symm
  have undo (M : Matrix (Fin 8) (Fin 8) ℂ) :
      (M.submatrix tripleIndex tripleIndex).submatrix tripleIndex.symm tripleIndex.symm=M := by
    ext i j
    change M (tripleIndex (tripleIndex.symm i)) (tripleIndex (tripleIndex.symm j))=M i j
    simp only [Equiv.apply_symm_apply]
  rw [undo] at upFull downFull
  exact ⟨upFull.nonneg,downFull.nonneg⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
