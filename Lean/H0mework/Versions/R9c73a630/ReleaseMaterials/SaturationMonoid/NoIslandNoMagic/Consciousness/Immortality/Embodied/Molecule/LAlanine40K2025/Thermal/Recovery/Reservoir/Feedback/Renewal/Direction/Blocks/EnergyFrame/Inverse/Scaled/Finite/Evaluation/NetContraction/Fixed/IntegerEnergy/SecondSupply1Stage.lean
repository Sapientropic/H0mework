import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondStagedActions

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def secondSupplyPulseTable : IntTable 64 64 :=
  toTable (sourceOrdinarySupplyPulseInt (0 : Basis) (2 : Basis) (by decide))
    pointerFin pointerFin

def stagedSecondSupply1Table : IntTable 64 8 :=
  applyActionTable secondSupplyPulseTable literalSecondEntranceTable

theorem staged_second_supply1_original :
    fromTable stagedSecondSupply1Table pointerFin nativeFin =
      sourceOrdinaryAfterSupply1Int (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondSupply1Table,apply_action_table_original,
    secondSupplyPulseTable,from_to_table,literal_second_entrance_original]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
