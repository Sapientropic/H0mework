import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondWeightedConsumer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def stagedSecondNineQuadraticTable : IntTable 4 4 :=
  toTable
    (multiply (fromTable literalSecondNineWeightedTable pairFin pointerFin)
      (submatrix (fromTable literalSecondNineTable pointerFin nativeFin)
        id chargedInjection)) pairFin pairFin

def stagedSecondElevenQuadraticTable : IntTable 4 4 :=
  toTable
    (multiply (fromTable literalSecondElevenWeightedTable pairFin pointerFin)
      (submatrix (fromTable literalSecondElevenTable pointerFin nativeFin)
        id chargedInjection)) pairFin pairFin

theorem staged_second_nine_quadratic_original :
    fromTable stagedSecondNineQuadraticTable pairFin pairFin =
      multiply
        (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (2 : Basis)
          (by decide))) (sourceOrdinaryPCInt (0 : Basis) (2 : Basis)))
        (sourceOrdinaryNineSelectedInt (0 : Basis) (2 : Basis) (by decide)) := by
  rw [stagedSecondNineQuadraticTable,from_to_table,
    literal_second_nine_weighted_original,literal_second_nine_original]
  rfl

theorem staged_second_eleven_quadratic_original :
    fromTable stagedSecondElevenQuadraticTable pairFin pairFin =
      multiply
        (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (2 : Basis)
          (by decide))) (sourceOrdinaryPCInt (0 : Basis) (2 : Basis)))
        (sourceOrdinaryElevenSelectedInt (0 : Basis) (2 : Basis) (by decide)) := by
  rw [stagedSecondElevenQuadraticTable,from_to_table,
    literal_second_eleven_weighted_original,literal_second_eleven_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
