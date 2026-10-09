import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.Weak
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

private theorem third_nine_upper_matrix :
    submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      fromTable upperNineTable ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_upper_actual_literal]

private theorem third_weak_upper_core_matrix :
    quantize (ordinaryLoadFullQ (0 : Basis) (3 : Basis) (by decide)) = fromTable loadFullTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (ordinaryLoadFullQ (0 : Basis) (3 : Basis) (by decide))) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_loadFullTable_source]

theorem third_weak_upper_actual_literal :
    toTable (submatrix (sourceOrdinaryAfterWeakInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) ordinaryFullFin nativeFin =
      upperWeakTable := by
  have h := (source_ordinary_after_weak_arms (0 : Basis) (3 : Basis) (by decide)).1
  rw [third_weak_upper_core_matrix, third_nine_upper_matrix] at h
  change submatrix (sourceOrdinaryAfterWeakInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id = upperWeakStage03 at h
  exact (congrArg (fun X => toTable X ordinaryFullFin nativeFin) h).trans
    third_weak_upper_staged_literal

private theorem third_nine_lower_matrix :
    submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      fromTable lowerNineTable ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_lower_actual_literal]

private theorem third_weak_lower_core_matrix :
    quantize (qscale phaseQ (ordinaryWeakFullQ (0 : Basis) (3 : Basis) (by decide))) = fromTable phaseWeakTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (qscale phaseQ (ordinaryWeakFullQ (0 : Basis) (3 : Basis) (by decide)))) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_phaseWeakTable_source]

theorem third_weak_lower_actual_literal :
    toTable (submatrix (sourceOrdinaryAfterWeakInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) ordinaryFullFin nativeFin =
      lowerWeakTable := by
  have h := (source_ordinary_after_weak_arms (0 : Basis) (3 : Basis) (by decide)).2
  rw [third_weak_lower_core_matrix, third_nine_lower_matrix] at h
  change submatrix (sourceOrdinaryAfterWeakInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id = lowerWeakStage03 at h
  exact (congrArg (fun X => toTable X ordinaryFullFin nativeFin) h).trans
    third_weak_lower_staged_literal

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
