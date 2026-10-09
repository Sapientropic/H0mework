import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondPCCoreLiteral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.PCCoreLiteral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem literal_second_pc_core_table :
    toTable sourceSecondPCCoreInt ordinaryFullFin ordinaryFullFin =
      literalSecondPCCoreTable :=
  int_table_ext literal_second_pc_core_re literal_second_pc_core_im

theorem literal_second_pc_core_original :
    fromTable literalSecondPCCoreTable ordinaryFullFin ordinaryFullFin =
      sourceSecondPCCoreInt := by
  rw [← literal_second_pc_core_table]
  exact from_to_table _ _ _

def literalSecondPCInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks
    (fromTable literalSecondPCCoreTable ordinaryFullFin ordinaryFullFin)
    sourceFirstZeroCoreInt sourceFirstZeroCoreInt
    (fromTable literalSecondPCCoreTable ordinaryFullFin ordinaryFullFin)

theorem literal_second_pc_original :
    literalSecondPCInt = sourceOrdinaryPCInt (0 : Basis) (2 : Basis) := by
  rw [source_second_pc_blocks,literalSecondPCInt,literal_second_pc_core_original]

theorem literal_second_pc_not_first :
    literalSecondPCCoreRe.get (0 : Fin 32) ≠
      literalPCCoreRe.get (0 : Fin 32) := by decide +kernel

theorem literal_second_pc_actual_error :
    ‖value literalSecondPCInt -
      (localPC (s((0 : Basis),2))).submatrix
        (coordinatePointer (s((0 : Basis),2))
          (ordinaryFullEquiv (0 : Basis) 2 (by decide)))
        (coordinatePointer (s((0 : Basis),2))
          (ordinaryFullEquiv (0 : Basis) 2 (by decide)))‖ ≤
      (64/10^30 : ℝ) := by
  rw [literal_second_pc_original]
  have h := quantize_error (ordinaryPCPointerQ (0 : Basis) (2 : Basis))
    (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])
  rw [ordinary_pc_pointer_value 0 2 (by decide)] at h
  exact h

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
