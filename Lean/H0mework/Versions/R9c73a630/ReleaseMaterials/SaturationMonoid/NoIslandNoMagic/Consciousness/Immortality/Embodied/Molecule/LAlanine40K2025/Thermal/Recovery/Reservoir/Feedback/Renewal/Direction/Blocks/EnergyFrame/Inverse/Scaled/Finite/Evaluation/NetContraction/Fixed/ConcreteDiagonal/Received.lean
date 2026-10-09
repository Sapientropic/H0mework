import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.Columns

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction Evaluate
open scoped Matrix BigOperators

theorem source_diagonal_received_concrete (a : Basis) :
    sourceDiagonalReceivedInt a = quantize (diagonalReceivedQ a) := by
  apply congrArg quantize
  apply Evaluate.qvalue_injective
  rw [sourceDiagonalReceivedQ,qvalue_submatrix,receivedBlockQ_value,
    diagonalReceivedQ_value]
  simp only [localReceivedWord,restrict,Matrix.submatrix_submatrix]
  rfl

def firstSixEntranceInt (a : Fin 6) :
    MatrixInt (DiagonalFull ⊕ DiagonalFull) (Fin 2 × Fin 2) :=
  multiply (quantize (firstSixSourceColumnsQ a))
    (quantize (diagonalReceivedQ (firstSixBasis a)))

theorem first_six_entrance_source (a : Fin 6) :
    sourceDiagonalEntranceInt (firstSixBasis a) (first_six_different a) =
      firstSixEntranceInt a := by
  unfold sourceDiagonalEntranceInt firstSixEntranceInt
  rw [first_six_columns_source,source_diagonal_received_concrete]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
