import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Restriction

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem normalized_submatrix {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : κ → ι) (injective : Function.Injective f) (tau mu : ℝ) (A : Matrix ι ι ℂ) :
    (normalizedAt tau mu A).submatrix f f=normalizedAt tau mu (A.submatrix f f) := by
  ext i j
  simp only [normalizedAt,Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply]
  rw [if_congr injective.eq_iff rfl rfl]

def firstBlockEffect : Matrix (Fin 8) (Fin 8) ℂ := normalizedAt rationalRegularizer (480362644764/10^10) block0

theorem first_index_injective : Function.Injective (orbitPCE 0 1) := by
  intro a b same
  apply (offDiagonalPCEEquiv 0 1 (by decide)).injective
  exact Subtype.ext same

theorem first_source_effect : finiteEffect.submatrix (orbitPCE 0 1) (orbitPCE 0 1)=
    firstBlockEffect.submatrix tripleIndex tripleIndex := by
  rw [finiteEffect,normalized_submatrix _ first_index_injective,original_rational_block 0 1 (by decide),source_block0]
  exact (normalized_submatrix tripleIndex tripleIndex.injective _ _ block0).symm

theorem first_source_complement : (1-finiteEffect).submatrix (orbitPCE 0 1) (orbitPCE 0 1)=
    (1-firstBlockEffect).submatrix tripleIndex tripleIndex := by
  simp only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one _ first_index_injective,first_source_effect,
    Matrix.submatrix_one _ tripleIndex.injective]

theorem first_block_positive : 0 ≤ firstBlockEffect ∧ 0 ≤ 1-firstBlockEffect := by
  have hermitian : block0.IsHermitian := by
    rw [← rational_block0]
    exact cast_hermitian _ _ (by decide +kernel) (by decide +kernel)
  exact ⟨normalized_positive block0 hermitian _ _ rational_regularizer_positive block0_norm_upper,
    normalized_complement_positive block0 hermitian _ _ rational_regularizer_positive block0_norm_upper⟩

theorem first_effect_cast : cast (effectReal real0 1) (effectImag imag0 1)=firstBlockEffect := by
  rw [effect_cast,rational_block0]
  simp only [Rat.cast_one,one_smul,firstBlockEffect]

theorem first_complement_cast : cast (effectReal real0 (-1)) (effectImag imag0 (-1))=1-firstBlockEffect := by
  rw [effect_cast,rational_block0]
  simp only [Rat.cast_neg,Rat.cast_one,neg_one_smul,firstBlockEffect,normalized_complement]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
