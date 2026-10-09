import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.PCCoreLiteral
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem literal_pc_core_table :
    toTable sourceFirstPCCoreInt ordinaryFullFin ordinaryFullFin=literalPCCoreTable :=
  int_table_ext literal_pc_core_re literal_pc_core_im

theorem literal_pc_core_original :
    fromTable literalPCCoreTable ordinaryFullFin ordinaryFullFin=sourceFirstPCCoreInt := by
  rw [← literal_pc_core_table]
  exact from_to_table _ _ _

def literalFirstPCInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks
    (fromTable literalPCCoreTable ordinaryFullFin ordinaryFullFin)
    sourceFirstZeroCoreInt sourceFirstZeroCoreInt
    (fromTable literalPCCoreTable ordinaryFullFin ordinaryFullFin)

theorem literal_first_pc_original : literalFirstPCInt=sourceFirstPCInt := by
  rw [source_first_pc_blocks,literalFirstPCInt,literal_pc_core_original]

theorem literal_first_pc_source_error :
    ‖value literalFirstPCInt-
      qvalue (ordinaryPCPointerQ (0 : Basis) (1 : Basis))‖ ≤ (64/10^30 : ℝ) := by
  rw [literal_first_pc_original]
  exact quantize_error _ (by norm_num [OrdinaryFull]) (by norm_num [OrdinaryFull])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
