import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.WeightedConsumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

def stagedFirstNineQuadraticTable : IntTable 4 4 :=
  toTable
    (multiply (fromTable literalNineWeightedTable pairFin pointerFin)
      (submatrix (fromTable literalFirstNineTable pointerFin nativeFin)
        id chargedInjection)) pairFin pairFin

def stagedFirstElevenQuadraticTable : IntTable 4 4 :=
  toTable
    (multiply (fromTable literalElevenWeightedTable pairFin pointerFin)
      (submatrix (fromTable literalFirstElevenTable pointerFin nativeFin)
        id chargedInjection)) pairFin pairFin

theorem staged_first_nine_quadratic_original :
    fromTable stagedFirstNineQuadraticTable pairFin pairFin =
      multiply (multiply (adjoint sourceFirstNineSelectedInt) sourceFirstPCInt)
        sourceFirstNineSelectedInt := by
  rw [stagedFirstNineQuadraticTable,from_to_table,
    literal_nine_weighted_original,literal_first_nine_original]
  rfl

theorem staged_first_eleven_quadratic_original :
    fromTable stagedFirstElevenQuadraticTable pairFin pairFin =
      multiply (multiply (adjoint sourceFirstElevenSelectedInt) sourceFirstPCInt)
        sourceFirstElevenSelectedInt := by
  rw [stagedFirstElevenQuadraticTable,from_to_table,
    literal_eleven_weighted_original,literal_first_eleven_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
