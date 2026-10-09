import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.EntranceConsumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

def applyActionTable (P : IntTable 64 64) (V : IntTable 64 8) : IntTable 64 8 :=
  toTable (multiply (fromTable P pointerFin pointerFin)
    (fromTable V pointerFin nativeFin)) pointerFin nativeFin

theorem apply_action_table_original (P : IntTable 64 64) (V : IntTable 64 8) :
    fromTable (applyActionTable P V) pointerFin nativeFin =
      multiply (fromTable P pointerFin pointerFin) (fromTable V pointerFin nativeFin) := by
  exact from_to_table _ _ _

def stagedFirstActionTables : IntTable 64 8 × IntTable 64 8 := Id.run do
  let supplyPulse := toTable sourceFirstSupplyPulseInt pointerFin pointerFin
  let loadPulse := toTable sourceFirstLoadPulseInt pointerFin pointerFin
  let weakPulse := toTable sourceFirstWeakPulseInt pointerFin pointerFin
  let entrance := literalFirstEntranceTable
  let afterSupply1 := applyActionTable supplyPulse entrance
  let afterSupply2 := applyActionTable supplyPulse afterSupply1
  let nine := applyActionTable loadPulse afterSupply2
  let afterWeak := applyActionTable weakPulse nine
  let eleven := applyActionTable loadPulse afterWeak
  return (nine,eleven)

def stagedFirstNineTable : IntTable 64 8 := stagedFirstActionTables.1
def stagedFirstElevenTable : IntTable 64 8 := stagedFirstActionTables.2

theorem staged_first_nine_original :
    fromTable stagedFirstNineTable pointerFin nativeFin=sourceFirstNineInt := by
  simp [stagedFirstNineTable,stagedFirstActionTables,apply_action_table_original,
    from_to_table,literal_first_entrance_original,
    sourceFirstNineInt,sourceFirstAfterSupply2Int,sourceFirstAfterSupply1Int]

theorem staged_first_eleven_original :
    fromTable stagedFirstElevenTable pointerFin nativeFin=sourceFirstElevenInt := by
  simp [stagedFirstElevenTable,stagedFirstActionTables,apply_action_table_original,
    from_to_table,literal_first_entrance_original,
    sourceFirstElevenInt,sourceFirstAfterWeakInt,sourceFirstNineInt,
    sourceFirstAfterSupply2Int,sourceFirstAfterSupply1Int]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
