import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondEntranceConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.StagedActions

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def stagedSecondActionTables : IntTable 64 8 × IntTable 64 8 := Id.run do
  let supplyPulse := toTable
    (sourceOrdinarySupplyPulseInt (0 : Basis) (2 : Basis) (by decide))
    pointerFin pointerFin
  let loadPulse := toTable
    (sourceOrdinaryLoadPulseInt (0 : Basis) (2 : Basis) (by decide))
    pointerFin pointerFin
  let weakPulse := toTable
    (sourceOrdinaryWeakPulseInt (0 : Basis) (2 : Basis) (by decide))
    pointerFin pointerFin
  let entrance := literalSecondEntranceTable
  let afterSupply1 := applyActionTable supplyPulse entrance
  let afterSupply2 := applyActionTable supplyPulse afterSupply1
  let nine := applyActionTable loadPulse afterSupply2
  let afterWeak := applyActionTable weakPulse nine
  let eleven := applyActionTable loadPulse afterWeak
  return (nine,eleven)

def stagedSecondNineTable : IntTable 64 8 := stagedSecondActionTables.1
def stagedSecondElevenTable : IntTable 64 8 := stagedSecondActionTables.2

theorem staged_second_nine_original :
    fromTable stagedSecondNineTable pointerFin nativeFin =
      sourceOrdinaryNineInt (0 : Basis) (2 : Basis) (by decide) := by
  simp [stagedSecondNineTable,stagedSecondActionTables,apply_action_table_original,
    from_to_table,literal_second_entrance_original,
    sourceOrdinaryNineInt,sourceOrdinaryAfterSupply2Int,
    sourceOrdinaryAfterSupply1Int]

theorem staged_second_eleven_original :
    fromTable stagedSecondElevenTable pointerFin nativeFin =
      sourceOrdinaryElevenInt (0 : Basis) (2 : Basis) (by decide) := by
  simp [stagedSecondElevenTable,stagedSecondActionTables,apply_action_table_original,
    from_to_table,literal_second_entrance_original,
    sourceOrdinaryElevenInt,sourceOrdinaryAfterWeakInt,sourceOrdinaryNineInt,
    sourceOrdinaryAfterSupply2Int,sourceOrdinaryAfterSupply1Int]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
