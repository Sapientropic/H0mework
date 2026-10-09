import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.Weighted
set_option autoImplicit false
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

private theorem third_pc_core_matrix :
    quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)) =
      fromTable pcFullTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis))) ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_pcFullTable_source]

private theorem third_nine_upper_matrix :
    submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      fromTable upperNineTable ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_upper_actual_literal]

private theorem third_nine_lower_matrix :
    submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      fromTable lowerNineTable ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_lower_actual_literal]

private theorem third_eleven_upper_matrix :
    submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      fromTable upperElevenTable ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_eleven_upper_actual_literal]

private theorem third_eleven_lower_matrix :
    submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      fromTable lowerElevenTable ordinaryFullFin nativeFin := by
  calc
    _ = fromTable (toTable (submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) ordinaryFullFin nativeFin) ordinaryFullFin nativeFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_eleven_lower_actual_literal]

private theorem third_nine_upper_selected_matrix :
    submatrix (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      submatrix (fromTable upperNineTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryNineSelectedInt
  change submatrix (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) id chargedInjection = _
  rw [third_nine_upper_matrix]

private theorem third_nine_lower_selected_matrix :
    submatrix (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      submatrix (fromTable lowerNineTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryNineSelectedInt
  change submatrix (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) id chargedInjection = _
  rw [third_nine_lower_matrix]

private theorem third_eleven_upper_selected_matrix :
    submatrix (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      submatrix (fromTable upperElevenTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryElevenSelectedInt
  change submatrix (submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) id chargedInjection = _
  rw [third_eleven_upper_matrix]

private theorem third_eleven_lower_selected_matrix :
    submatrix (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      submatrix (fromTable lowerElevenTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryElevenSelectedInt
  change submatrix (submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) id chargedInjection = _
  rw [third_eleven_lower_matrix]

theorem third_nine_upper_weighted_actual_literal :
    toTable (submatrix (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inl) pairFin ordinaryFullFin =
      upperNineWeightedTable := by
  rw [ordinary_pc_pointer_blocks, third_pc_core_matrix]
  have h := multiply_block_pulse_upper
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
  rw [third_pc_core_matrix] at h
  have select := third_nine_upper_selected_matrix
  have adj : submatrix (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide))) id Sum.inl =
      adjoint (submatrix (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) := by rfl
  rw [adj, select] at h
  exact (congrArg (fun X => toTable X pairFin ordinaryFullFin) h).trans
    third_upperNineWeighted_staged_literal

theorem third_nine_lower_weighted_actual_literal :
    toTable (submatrix (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inr) pairFin ordinaryFullFin =
      lowerNineWeightedTable := by
  rw [ordinary_pc_pointer_blocks, third_pc_core_matrix]
  have h := multiply_block_pulse_lower
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
  rw [third_pc_core_matrix] at h
  have select := third_nine_lower_selected_matrix
  have adj : submatrix (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide))) id Sum.inr =
      adjoint (submatrix (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) := by rfl
  rw [adj, select] at h
  exact (congrArg (fun X => toTable X pairFin ordinaryFullFin) h).trans
    third_lowerNineWeighted_staged_literal

theorem third_eleven_upper_weighted_actual_literal :
    toTable (submatrix (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inl) pairFin ordinaryFullFin =
      upperElevenWeightedTable := by
  rw [ordinary_pc_pointer_blocks, third_pc_core_matrix]
  have h := multiply_block_pulse_upper
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
  rw [third_pc_core_matrix] at h
  have select := third_eleven_upper_selected_matrix
  have adj : submatrix (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide))) id Sum.inl =
      adjoint (submatrix (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) := by rfl
  rw [adj, select] at h
  exact (congrArg (fun X => toTable X pairFin ordinaryFullFin) h).trans
    third_upperElevenWeighted_staged_literal

theorem third_eleven_lower_weighted_actual_literal :
    toTable (submatrix (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inr) pairFin ordinaryFullFin =
      lowerElevenWeightedTable := by
  rw [ordinary_pc_pointer_blocks, third_pc_core_matrix]
  have h := multiply_block_pulse_lower
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (quantize (ordinaryPCFullQ (0 : Basis) (3 : Basis)))
    (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
  rw [third_pc_core_matrix] at h
  have select := third_eleven_lower_selected_matrix
  have adj : submatrix (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide))) id Sum.inr =
      adjoint (submatrix (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) := by rfl
  rw [adj, select] at h
  exact (congrArg (fun X => toTable X pairFin ordinaryFullFin) h).trans
    third_lowerElevenWeighted_staged_literal

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
