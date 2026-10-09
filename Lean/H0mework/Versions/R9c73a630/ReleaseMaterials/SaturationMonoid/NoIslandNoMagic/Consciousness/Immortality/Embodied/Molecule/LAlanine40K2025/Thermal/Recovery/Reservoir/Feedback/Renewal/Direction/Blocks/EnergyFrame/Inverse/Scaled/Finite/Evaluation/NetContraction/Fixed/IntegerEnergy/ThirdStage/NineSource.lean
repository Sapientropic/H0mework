import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.Nine
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

private theorem third_supply2_upper_matrix :
    submatrix (sourceOrdinaryAfterSupply2Int (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      fromTable upperSupply2Table ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryAfterSupply2Int (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_supply2_upper_actual_literal]

private theorem third_nine_upper_core_matrix :
    quantize (ordinaryLoadFullQ (0 : Basis) (3 : Basis) (by decide)) = fromTable loadFullTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (ordinaryLoadFullQ (0 : Basis) (3 : Basis) (by decide))) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_loadFullTable_source]

theorem third_nine_upper_actual_literal :
    toTable (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) ordinaryFullFin nativeFin =
      upperNineTable := by
  have h := (source_ordinary_nine_arms (0 : Basis) (3 : Basis) (by decide)).1
  rw [third_nine_upper_core_matrix, third_supply2_upper_matrix] at h
  change submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id = upperNineStage03 at h
  exact (congrArg (fun X => toTable X ordinaryFullFin nativeFin) h).trans
    third_nine_upper_staged_literal

private theorem third_supply2_lower_matrix :
    submatrix (sourceOrdinaryAfterSupply2Int (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      fromTable lowerSupply2Table ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryAfterSupply2Int (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_supply2_lower_actual_literal]

private theorem third_nine_lower_core_matrix :
    quantize (qscale phaseQ (ordinaryLoadFullQ (0 : Basis) (3 : Basis) (by decide))) = fromTable phaseLoadTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (qscale phaseQ (ordinaryLoadFullQ (0 : Basis) (3 : Basis) (by decide)))) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_phaseLoadTable_source]

theorem third_nine_lower_actual_literal :
    toTable (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) ordinaryFullFin nativeFin =
      lowerNineTable := by
  have h := (source_ordinary_nine_arms (0 : Basis) (3 : Basis) (by decide)).2
  rw [third_nine_lower_core_matrix, third_supply2_lower_matrix] at h
  change submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id = lowerNineStage03 at h
  exact (congrArg (fun X => toTable X ordinaryFullFin nativeFin) h).trans
    third_nine_lower_staged_literal

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
