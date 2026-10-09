import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondPCCoreConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def stagedSecondNineWeightedTable : IntTable 4 64 :=
  toTable
    (multiply
      (adjoint (submatrix (fromTable literalSecondNineTable pointerFin nativeFin)
        id chargedInjection)) literalSecondPCInt) pairFin pointerFin

def stagedSecondElevenWeightedTable : IntTable 4 64 :=
  toTable
    (multiply
      (adjoint (submatrix (fromTable literalSecondElevenTable pointerFin nativeFin)
        id chargedInjection)) literalSecondPCInt) pairFin pointerFin

theorem staged_second_nine_weighted_original :
    fromTable stagedSecondNineWeightedTable pairFin pointerFin =
      multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (2 : Basis)
        (by decide))) (sourceOrdinaryPCInt (0 : Basis) (2 : Basis)) := by
  rw [stagedSecondNineWeightedTable,from_to_table,
    literal_second_nine_original,literal_second_pc_original]
  rfl

theorem staged_second_eleven_weighted_original :
    fromTable stagedSecondElevenWeightedTable pairFin pointerFin =
      multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (2 : Basis)
        (by decide))) (sourceOrdinaryPCInt (0 : Basis) (2 : Basis)) := by
  rw [stagedSecondElevenWeightedTable,from_to_table,
    literal_second_eleven_original,literal_second_pc_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
