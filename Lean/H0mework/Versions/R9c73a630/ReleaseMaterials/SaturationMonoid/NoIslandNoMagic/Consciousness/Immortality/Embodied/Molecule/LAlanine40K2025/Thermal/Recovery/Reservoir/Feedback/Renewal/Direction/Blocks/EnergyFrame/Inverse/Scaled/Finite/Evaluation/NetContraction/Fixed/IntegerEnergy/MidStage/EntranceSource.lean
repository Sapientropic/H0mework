import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.Rotated
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.InputSourceLink
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.InputSupply
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.Energy

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def midChargedEntranceCached :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) := Id.run do
  let rotatedPlus := fromTable midRotatedPlusTable nativeFin nativeFin
  let rotatedMinus := fromTable midRotatedMinusTable nativeFin nativeFin
  let rolePlus := roleBlocksInt (bodyLiftIdentityInt rotatedPlus)
    (donorLiftIdentityInt sourceDonorRootRotatedInt)
  let roleMinus := roleBlocksInt (bodyLiftIdentityInt rotatedMinus)
    (donorLiftIdentityInt sourceDonorComplementRotatedInt)
  let pointer := intFourBlocks rolePlus (intNeg roleMinus) roleMinus rolePlus
  let supply := fromTable midSupplyTable ordinaryFullFin ordinaryFullFin
  let columns := multiply (submatrix pointer id Sum.inl)
    (submatrix supply id ordinaryInjection)
  let received := fromTable midReceivedTable nativeFin nativeFin
  return multiply columns (submatrix received id chargedInjection)

private theorem mid_rotated_plus_source :
    sourceOrdinaryRootRotatedInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midRotatedPlusTable nativeFin nativeFin := by
  rw [sourceOrdinaryRootRotatedInt, mid_free_int_table, mid_root_int_table]
  calc
    _ = fromTable (toTable (rotateInt (fromTable midFreeTable nativeFin nativeFin)
      (fromTable midRootTable nativeFin nativeFin)) nativeFin nativeFin)
      nativeFin nativeFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_rotated_plus_literal]

private theorem mid_rotated_minus_source :
    sourceOrdinaryComplementRotatedInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midRotatedMinusTable nativeFin nativeFin := by
  rw [sourceOrdinaryComplementRotatedInt, mid_free_int_table, mid_complement_int_table]
  calc
    _ = fromTable (toTable (rotateInt (fromTable midFreeTable nativeFin nativeFin)
      (fromTable midComplementTable nativeFin nativeFin)) nativeFin nativeFin)
      nativeFin nativeFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_rotated_minus_literal]

theorem mid_charged_entrance_source :
    chargedEntranceInt (0 : Basis) (6 : Basis) (by decide) =
      midChargedEntranceCached := by
  unfold chargedEntranceInt sourceOrdinaryColumnsInt sourceOrdinaryPointerColumnsInt
    sourceOrdinarySupplyChargedInt sourceOrdinaryPointerInt
    sourceOrdinaryRootRoleInt sourceOrdinaryComplementRoleInt
  rw [mid_rotated_plus_source, mid_rotated_minus_source,
    mid_supply_int_table, mid_received_int_table]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
