import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.Ordinary
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Certificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def OrdinaryPair (a b : Basis) :=
  RootGram (effectReal (ordinary a b) 1) (effectImag (0 : Matrix (Fin 8) (Fin 8) ℚ) 1) ×
    RootGram (effectReal (ordinary a b) (-1)) (effectImag (0 : Matrix (Fin 8) (Fin 8) ℚ) (-1))

theorem ordinary_first : ordinary 0 1=real0 := by decide +kernel

def firstPair : OrdinaryPair 0 1 := by
  have zeroImag : imag0=(0 : Matrix (Fin 8) (Fin 8) ℚ) := by decide +kernel
  refine ⟨⟨FirstPlus.factor,0,?_⟩,⟨FirstMinus.factor,0,?_⟩⟩
  · rw [ordinary_first]
    have paid := FirstPlus.checked.trans (show ((1/10^7 : ℚ)*(1/10^7))^2 ≤ ((2/10^7 : ℚ)*(2/10^7))^2 by norm_num)
    simpa only [zeroImag] using paid
  · rw [ordinary_first]
    have paid := FirstMinus.checked.trans (show ((1/10^7 : ℚ)*(1/10^7))^2 ≤ ((2/10^7 : ℚ)*(2/10^7))^2 by norm_num)
    simpa only [zeroImag] using paid

theorem OrdinaryPair.bounds {a b : Basis} (G : OrdinaryPair a b) (distinct : a ≠ b) :
    ‖CFC.sqrt (ordinaryEffect a b 1)-G.1.value‖ ≤ (2/10^7 : ℝ) ∧
      ‖CFC.sqrt (ordinaryEffect a b (-1))-G.2.value‖ ≤ (2/10^7 : ℝ) :=
  ⟨G.1.error (ordinary_positive a b distinct).1,G.2.error (ordinary_positive a b distinct).2⟩

theorem OrdinaryPair.source_bounds {a b : Basis} (G : OrdinaryPair a b) (distinct : a ≠ b) :
    ‖(CFC.sqrt finiteEffect).submatrix (orbitPCE a b) (orbitPCE a b)-G.1.value.submatrix tripleIndex tripleIndex‖ ≤ (2/10^7 : ℝ) ∧
    ‖(CFC.sqrt (1-finiteEffect)).submatrix (orbitPCE a b) (orbitPCE a b)-G.2.value.submatrix tripleIndex tripleIndex‖ ≤ (2/10^7 : ℝ) := by
  constructor
  · rw [original_finite_root_restriction a b distinct,ordinary_effect_source a b distinct,
      ← reindex_sqrt tripleIndex (ordinaryEffect a b 1) (Matrix.nonneg_iff_posSemidef.mp (ordinary_positive a b distinct).1)]
    change ‖(CFC.sqrt (ordinaryEffect a b 1)-G.1.value).submatrix tripleIndex tripleIndex‖ ≤ _
    rw [Finite.reindex_norm]
    exact (G.bounds distinct).1
  · rw [original_finite_complement_restriction a b distinct,ordinary_complement_source a b distinct,
      ← reindex_sqrt tripleIndex (ordinaryEffect a b (-1)) (Matrix.nonneg_iff_posSemidef.mp (ordinary_positive a b distinct).2)]
    change ‖(CFC.sqrt (ordinaryEffect a b (-1))-G.2.value).submatrix tripleIndex tripleIndex‖ ≤ _
    rw [Finite.reindex_norm]
    exact (G.bounds distinct).2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
