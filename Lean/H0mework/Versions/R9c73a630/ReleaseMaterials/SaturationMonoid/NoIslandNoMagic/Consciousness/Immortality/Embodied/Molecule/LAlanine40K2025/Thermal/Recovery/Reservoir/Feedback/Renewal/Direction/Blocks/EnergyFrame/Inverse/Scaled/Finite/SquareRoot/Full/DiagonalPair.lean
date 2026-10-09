import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full.DonorEffect
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Certificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
open Propagation.Interface Load.Source Scaled.Order RationalMatrix
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def DiagonalPair (a : Fin 97) :=
  RootGram (effectReal (diagonal a) 1) (effectImag (0 : Matrix (Fin 4) (Fin 4) ℚ) 1) ×
    RootGram (effectReal (diagonal a) (-1)) (effectImag (0 : Matrix (Fin 4) (Fin 4) ℚ) (-1))

def DonorPair := RootGram (effectReal real4 1) (effectImag imag4 1) ×
  RootGram (effectReal real4 (-1)) (effectImag imag4 (-1))

theorem DiagonalPair.bounds {a : Fin 97} (G : DiagonalPair a) :
    ‖CFC.sqrt (diagonalEffect a 1)-G.1.value‖ ≤ (2/10^7 : ℝ) ∧
      ‖CFC.sqrt (diagonalEffect a (-1))-G.2.value‖ ≤ (2/10^7 : ℝ) :=
  ⟨G.1.error (diagonal_positive a).1,G.2.error (diagonal_positive a).2⟩

theorem DiagonalPair.source_bounds {a : Fin 97} (G : DiagonalPair a) :
    ‖(CFC.sqrt finiteEffect).submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)-G.1.value.submatrix pairIndex pairIndex‖ ≤ (2/10^7 : ℝ) ∧
    ‖(CFC.sqrt (1-finiteEffect)).submatrix (diagonalPCE a.castSucc) (diagonalPCE a.castSucc)-G.2.value.submatrix pairIndex pairIndex‖ ≤ (2/10^7 : ℝ) := by
  constructor
  · rw [original_diagonal_root_restriction,diagonal_effect_source,
      ← reindex_sqrt pairIndex (diagonalEffect a 1) (Matrix.nonneg_iff_posSemidef.mp (diagonal_positive a).1)]
    change ‖(CFC.sqrt (diagonalEffect a 1)-G.1.value).submatrix pairIndex pairIndex‖ ≤ _
    rw [Finite.reindex_norm]
    exact G.bounds.1
  · rw [original_diagonal_complement_restriction,diagonal_complement_source,
      ← reindex_sqrt pairIndex (diagonalEffect a (-1)) (Matrix.nonneg_iff_posSemidef.mp (diagonal_positive a).2)]
    change ‖(CFC.sqrt (diagonalEffect a (-1))-G.2.value).submatrix pairIndex pairIndex‖ ≤ _
    rw [Finite.reindex_norm]
    exact G.bounds.2

theorem DonorPair.bounds (G : DonorPair) :
    ‖CFC.sqrt (donorEffect 1)-G.1.value‖ ≤ (2/10^7 : ℝ) ∧
      ‖CFC.sqrt (donorEffect (-1))-G.2.value‖ ≤ (2/10^7 : ℝ) :=
  ⟨G.1.error donor_positive.1,G.2.error donor_positive.2⟩

theorem DonorPair.source_bounds (G : DonorPair) :
    ‖(CFC.sqrt finiteEffect).submatrix (diagonalPCE 97) (diagonalPCE 97)-G.1.value.submatrix pairIndex pairIndex‖ ≤ (2/10^7 : ℝ) ∧
    ‖(CFC.sqrt (1-finiteEffect)).submatrix (diagonalPCE 97) (diagonalPCE 97)-G.2.value.submatrix pairIndex pairIndex‖ ≤ (2/10^7 : ℝ) := by
  constructor
  · rw [original_diagonal_root_restriction,donor_effect_source,
      ← reindex_sqrt pairIndex (donorEffect 1) (Matrix.nonneg_iff_posSemidef.mp donor_positive.1)]
    change ‖(CFC.sqrt (donorEffect 1)-G.1.value).submatrix pairIndex pairIndex‖ ≤ _
    rw [Finite.reindex_norm]
    exact G.bounds.1
  · rw [original_diagonal_complement_restriction,donor_complement_source,
      ← reindex_sqrt pairIndex (donorEffect (-1)) (Matrix.nonneg_iff_posSemidef.mp donor_positive.2)]
    change ‖(CFC.sqrt (donorEffect (-1))-G.2.value).submatrix pairIndex pairIndex‖ ≤ _
    rw [Finite.reindex_norm]
    exact G.bounds.2

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.SquareRoot.Full
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
