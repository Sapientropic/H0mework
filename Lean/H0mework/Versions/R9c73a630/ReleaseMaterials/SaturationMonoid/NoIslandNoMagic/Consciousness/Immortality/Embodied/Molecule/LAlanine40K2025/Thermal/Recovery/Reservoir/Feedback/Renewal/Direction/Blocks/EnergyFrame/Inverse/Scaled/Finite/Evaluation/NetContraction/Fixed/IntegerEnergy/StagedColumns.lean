import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.PointerCertificate
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

def stagedFirstColumnsTable : IntTable 64 8 := Id.run do
  let pointerTable := literalFirstPointerTable
  let supplyTable := toTable sourceFirstSupplyInt ordinaryFullFin ordinaryFullFin
  let pointer := fromTable pointerTable pointerFin pointerFin
  let supply := fromTable supplyTable ordinaryFullFin ordinaryFullFin
  return toTable
    (multiply (submatrix pointer id Sum.inl) (submatrix supply id ordinaryInjection))
    pointerFin nativeFin

theorem staged_first_columns_original :
    fromTable stagedFirstColumnsTable pointerFin nativeFin=sourceFirstColumnsInt := by
  simp [stagedFirstColumnsTable,literal_first_pointer_original,
    from_to_table,sourceFirstColumnsInt,sourceFirstPointerColumnsInt,
    sourceFirstSupplyChargedInt]

def stagedFirstEntranceTable : IntTable 64 8 := Id.run do
  let columnsTable := stagedFirstColumnsTable
  let receivedTable := toTable sourceFirstReceivedInt nativeFin nativeFin
  let columns := fromTable columnsTable pointerFin nativeFin
  let received := fromTable receivedTable nativeFin nativeFin
  return toTable (multiply columns received) pointerFin nativeFin

theorem staged_first_entrance_original :
    fromTable stagedFirstEntranceTable pointerFin nativeFin=sourceFirstEntranceInt := by
  simp [stagedFirstEntranceTable,staged_first_columns_original,
    from_to_table,sourceFirstEntranceInt]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
