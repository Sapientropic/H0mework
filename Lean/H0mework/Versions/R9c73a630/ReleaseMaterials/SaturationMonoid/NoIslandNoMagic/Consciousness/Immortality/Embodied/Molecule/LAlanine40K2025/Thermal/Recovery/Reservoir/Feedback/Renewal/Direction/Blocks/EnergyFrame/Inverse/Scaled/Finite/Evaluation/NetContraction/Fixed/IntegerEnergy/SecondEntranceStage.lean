import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondColumnsConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformEntranceSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def secondLiteralEntranceInt :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex :=
  multiply (fromTable literalSecondColumnsTable pointerFin nativeFin)
    (sourceOrdinaryReceivedInt (0 : Basis) (2 : Basis) (by decide))

theorem second_literal_entrance_original :
    secondLiteralEntranceInt =
      sourceOrdinaryEntranceInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [secondLiteralEntranceInt,literal_second_columns_original]
  rfl

def stagedSecondEntranceTable : IntTable 64 8 :=
  toTable secondLiteralEntranceInt pointerFin nativeFin

theorem staged_second_entrance_original :
    fromTable stagedSecondEntranceTable pointerFin nativeFin =
      sourceOrdinaryEntranceInt (0 : Basis) (2 : Basis) (by decide) := by
  rw [stagedSecondEntranceTable,from_to_table,second_literal_entrance_original]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
