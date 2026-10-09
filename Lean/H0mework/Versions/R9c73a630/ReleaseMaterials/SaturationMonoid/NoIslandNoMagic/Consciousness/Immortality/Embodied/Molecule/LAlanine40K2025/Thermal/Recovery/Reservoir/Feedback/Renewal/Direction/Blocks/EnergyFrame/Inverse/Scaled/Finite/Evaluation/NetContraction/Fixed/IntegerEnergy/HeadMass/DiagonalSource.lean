import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalProgram
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_diagonal_columns_actual (a : Basis) (different : a ≠ 97) :
    ‖value (sourceDiagonalColumnsInt a different)-
      sourceColumns (s(a,a)) (diagonalFullEquiv a different)
        diagonalInjection‖ ≤ (64/10^30 : ℝ) := by
  rw [← source_columns_value]
  exact quantize_error _ (by norm_num [DiagonalFull]) (by norm_num)

theorem source_diagonal_received_value (a : Basis) :
    qvalue (sourceDiagonalReceivedQ a)=
      (localReceivedWord (s(a,a))).submatrix
        (Scaled.Order.diagonalPCEEquiv a) (Scaled.Order.diagonalPCEEquiv a) := by
  rw [sourceDiagonalReceivedQ,qvalue_submatrix,receivedBlockQ_value]

theorem source_diagonal_received_error (a : Basis) :
    ‖value (sourceDiagonalReceivedInt a)-
      qvalue (sourceDiagonalReceivedQ a)‖ ≤ (64/10^30 : ℝ) :=
  quantize_error _ (by norm_num) (by norm_num)

theorem source_diagonal_load_value (a : Basis) (different : a ≠ 97) :
    qvalue (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))=
      coordinateLoad (s(a,a)) (diagonalFullEquiv a different) :=
  coordinate_load_value _ _

theorem source_diagonal_supply_value (a : Basis) (different : a ≠ 97) :
    qvalue (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))=
      coordinateSupply (s(a,a)) (diagonalFullEquiv a different) :=
  coordinate_supply_value _ _

theorem source_diagonal_weak_value (a : Basis) (different : a ≠ 97) :
    qvalue (coordinateWeakQ (s(a,a)) (diagonalFullEquiv a different))=
      coordinateWeak (s(a,a)) (diagonalFullEquiv a different) :=
  coordinate_weak_value _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
