import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondEntranceStage

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def memoSecondReceivedTable : IntTable 8 8 :=
  toTable (sourceOrdinaryReceivedInt (0 : Basis) (2 : Basis) (by decide))
    nativeFin nativeFin

def memoSecondEntranceTable : IntTable 64 8 := Id.run do
  let columns := fromTable literalSecondColumnsTable pointerFin nativeFin
  let received := fromTable memoSecondReceivedTable nativeFin nativeFin
  return toTable (multiply columns received) pointerFin nativeFin

theorem memo_second_entrance_original :
    fromTable memoSecondEntranceTable pointerFin nativeFin =
      sourceOrdinaryEntranceInt (0 : Basis) (2 : Basis) (by decide) := by
  simp [memoSecondEntranceTable,memoSecondReceivedTable,from_to_table,
    literal_second_columns_original,sourceOrdinaryEntranceInt]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
