import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondSupply2Certificate

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def secondLoadPulseTable : IntTable 64 64 :=
  toTable (sourceOrdinaryLoadPulseInt (0 : Basis) (2 : Basis) (by decide))
    pointerFin pointerFin

def stagedSecondNineLiteralTable : IntTable 64 8 :=
  applyActionTable secondLoadPulseTable literalSecondSupply2Table

theorem staged_second_nine_literal_original :
    fromTable stagedSecondNineLiteralTable pointerFin nativeFin =
      sourceOrdinaryNineInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondNineLiteralTable,apply_action_table_original,
    secondLoadPulseTable,from_to_table,literal_second_supply2_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
