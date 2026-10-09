import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.Columns

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

private theorem third_rootPlusTable_matrix :
    sourceOrdinaryRootInt (0 : Basis) (3 : Basis) (by decide) = fromTable rootPlusTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryRootInt (0 : Basis) (3 : Basis) (by decide)) nativeFin nativeFin) nativeFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_rootPlusTable_source]

private theorem third_rootMinusTable_matrix :
    sourceOrdinaryComplementInt (0 : Basis) (3 : Basis) (by decide) = fromTable rootMinusTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryComplementInt (0 : Basis) (3 : Basis) (by decide)) nativeFin nativeFin) nativeFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_rootMinusTable_source]

private theorem third_freeTable_matrix :
    sourceOrdinaryFreeInt (0 : Basis) (3 : Basis) (by decide) = fromTable freeTable nativeFin nativeFin := by
  calc
    _ = fromTable (toTable (sourceOrdinaryFreeInt (0 : Basis) (3 : Basis) (by decide)) nativeFin nativeFin) nativeFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_freeTable_source]

private theorem third_supplyTable_matrix :
    sourceOrdinarySupplyInt (0 : Basis) (3 : Basis) (by decide) = fromTable supplyTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (sourceOrdinarySupplyInt (0 : Basis) (3 : Basis) (by decide)) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by
      unfold sourceOrdinarySupplyInt
      rw [third_supplyTable_source]

theorem third_columns_actual_literal :
    toTable (sourceOrdinaryColumnsInt (0 : Basis) (3 : Basis) (by decide))
      pointerFin nativeFin = columnsTable := by
  have same : sourceOrdinaryColumnsInt (0 : Basis) (3 : Basis) (by decide) =
      stageColumns03 := by
    unfold sourceOrdinaryColumnsInt sourceOrdinaryPointerColumnsInt
      sourceOrdinarySupplyChargedInt sourceOrdinaryPointerInt
      sourceOrdinaryRootRoleInt sourceOrdinaryComplementRoleInt
      sourceOrdinaryRootRotatedInt sourceOrdinaryComplementRotatedInt
    rw [third_rootPlusTable_matrix, third_rootMinusTable_matrix,
      third_freeTable_matrix, third_supplyTable_matrix]
    simp only [stageColumns03]
    rfl
  exact (congrArg (fun X => toTable X pointerFin nativeFin) same).trans
    third_columns_staged_literal

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
