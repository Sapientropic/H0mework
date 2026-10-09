import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondBodyLiteral

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators

def stagedSecondNetTable : IntTable 4 4 :=
  toTable
    (sub (fromTable literalSecondElevenQuadraticTable pairFin pairFin)
      (fromTable literalSecondNineQuadraticTable pairFin pairFin)) pairFin pairFin

theorem staged_second_net_original :
    fromTable stagedSecondNetTable pairFin pairFin =
      sourceOrdinaryNetInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondNetTable,from_to_table,
    literal_second_eleven_quadratic_original,
    literal_second_nine_quadratic_original]
  rfl

def stagedSecondEnergyProductTable : IntTable 4 4 :=
  toTable
    (multiply (fromTable stagedSecondNetTable pairFin pairFin)
      (fromTable literalSecondBodyTable pairFin pairFin)) pairFin pairFin

theorem staged_second_energy_product_original :
    fromTable stagedSecondEnergyProductTable pairFin pairFin =
      sourceOrdinaryEnergyProductInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondEnergyProductTable,from_to_table,
    staged_second_net_original,literal_second_body_original]
  rfl

def stagedSecondGainNumeratorInt : Int :=
  ∑ i : Fin 2 × Fin 2,
    (fromTable stagedSecondEnergyProductTable pairFin pairFin).re i i

theorem staged_second_gain_original :
    stagedSecondGainNumeratorInt =
      sourceOrdinaryGainNumeratorInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondGainNumeratorInt,staged_second_energy_product_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
