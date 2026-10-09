import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.FirstPlus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.FirstMinus
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.FirstSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def firstRoot : Matrix (Fin 8) (Fin 8) ℂ := cast FirstPlus.factor 0*(cast FirstPlus.factor 0)ᴴ
def firstComplement : Matrix (Fin 8) (Fin 8) ℂ := cast FirstMinus.factor 0*(cast FirstMinus.factor 0)ᴴ

theorem first_root_error : ‖CFC.sqrt firstBlockEffect-firstRoot‖ ≤ (1/10^7 : ℝ) := by
  have paid := rational_gram_root (effectReal real0 1) (effectImag imag0 1) FirstPlus.factor 0
    (by rw [first_effect_cast]; exact first_block_positive.1) (1/10^7) (by norm_num) FirstPlus.checked
  rw [first_effect_cast] at paid
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,firstRoot] using paid

theorem first_complement_error : ‖CFC.sqrt (1-firstBlockEffect)-firstComplement‖ ≤ (1/10^7 : ℝ) := by
  have paid := rational_gram_root (effectReal real0 (-1)) (effectImag imag0 (-1)) FirstMinus.factor 0
    (by rw [first_complement_cast]; exact first_block_positive.2) (1/10^7) (by norm_num) FirstMinus.checked
  rw [first_complement_cast] at paid
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,firstComplement] using paid

theorem original_first_root_error :
    ‖(CFC.sqrt finiteEffect).submatrix (orbitPCE 0 1) (orbitPCE 0 1)-firstRoot.submatrix tripleIndex tripleIndex‖ ≤ (1/10^7 : ℝ) := by
  rw [original_finite_root_restriction 0 1 (by decide),first_source_effect,
    ← reindex_sqrt tripleIndex firstBlockEffect (Matrix.nonneg_iff_posSemidef.mp first_block_positive.1)]
  change ‖(CFC.sqrt firstBlockEffect-firstRoot).submatrix tripleIndex tripleIndex‖ ≤ _
  rw [Finite.reindex_norm]
  exact first_root_error

theorem original_first_complement_error :
    ‖(CFC.sqrt (1-finiteEffect)).submatrix (orbitPCE 0 1) (orbitPCE 0 1)-firstComplement.submatrix tripleIndex tripleIndex‖ ≤ (1/10^7 : ℝ) := by
  rw [original_finite_complement_restriction 0 1 (by decide),first_source_complement,
    ← reindex_sqrt tripleIndex (1-firstBlockEffect) (Matrix.nonneg_iff_posSemidef.mp first_block_positive.2)]
  change ‖(CFC.sqrt (1-firstBlockEffect)-firstComplement).submatrix tripleIndex tripleIndex‖ ≤ _
  rw [Finite.reindex_norm]
  exact first_complement_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
