import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.StagedEnergy
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

def stagedFirstNineWeightedTable : IntTable 4 64 :=
  toTable
    (multiply
      (adjoint (submatrix (fromTable literalFirstNineTable pointerFin nativeFin)
        id chargedInjection)) literalFirstPCInt) pairFin pointerFin

def stagedFirstElevenWeightedTable : IntTable 4 64 :=
  toTable
    (multiply
      (adjoint (submatrix (fromTable literalFirstElevenTable pointerFin nativeFin)
        id chargedInjection)) literalFirstPCInt) pairFin pointerFin

theorem staged_first_nine_weighted_original :
    fromTable stagedFirstNineWeightedTable pairFin pointerFin =
      multiply (adjoint sourceFirstNineSelectedInt) sourceFirstPCInt := by
  rw [stagedFirstNineWeightedTable,from_to_table,
    literal_first_nine_original,literal_first_pc_original]
  rfl

theorem staged_first_eleven_weighted_original :
    fromTable stagedFirstElevenWeightedTable pairFin pointerFin =
      multiply (adjoint sourceFirstElevenSelectedInt) sourceFirstPCInt := by
  rw [stagedFirstElevenWeightedTable,from_to_table,
    literal_first_eleven_original,literal_first_pc_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
