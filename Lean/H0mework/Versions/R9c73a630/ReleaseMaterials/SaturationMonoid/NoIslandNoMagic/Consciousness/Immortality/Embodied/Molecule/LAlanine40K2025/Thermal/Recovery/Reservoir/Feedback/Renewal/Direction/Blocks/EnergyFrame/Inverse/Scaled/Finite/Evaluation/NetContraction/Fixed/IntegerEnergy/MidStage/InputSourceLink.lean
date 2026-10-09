import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.InputRoot
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.InputSupply
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.Energy

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

theorem mid_root_int_table :
    sourceOrdinaryRootInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midRootTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryRootInt (0 : Basis) (6 : Basis) (by decide))
      nativeFin nativeFin) nativeFin nativeFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_root_source]

theorem mid_complement_int_table :
    sourceOrdinaryComplementInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midComplementTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryComplementInt (0 : Basis) (6 : Basis) (by decide))
      nativeFin nativeFin) nativeFin nativeFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_complement_source]

theorem mid_free_int_table :
    sourceOrdinaryFreeInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midFreeTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryFreeInt (0 : Basis) (6 : Basis) (by decide))
      nativeFin nativeFin) nativeFin nativeFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_free_source]

theorem mid_supply_int_table :
    sourceOrdinarySupplyInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midSupplyTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (sourceOrdinarySupplyInt (0 : Basis) (6 : Basis) (by decide))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [sourceOrdinarySupplyInt, mid_supply_source]

theorem mid_received_int_table :
    sourceOrdinaryReceivedInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midReceivedTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryReceivedInt (0 : Basis) (6 : Basis) (by decide))
      nativeFin nativeFin) nativeFin nativeFin := (from_to_table _ _ _).symm
    _ = _ := by rw [sourceOrdinaryReceivedInt, mid_received_source]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
