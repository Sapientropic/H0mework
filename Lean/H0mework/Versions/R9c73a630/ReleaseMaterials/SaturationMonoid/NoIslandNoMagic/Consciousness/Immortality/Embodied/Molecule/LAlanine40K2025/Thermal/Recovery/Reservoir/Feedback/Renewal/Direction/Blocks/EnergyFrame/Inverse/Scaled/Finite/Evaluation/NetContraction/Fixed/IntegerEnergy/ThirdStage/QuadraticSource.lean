import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ThirdStage.Quadratic
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

private theorem third_nine_upper_selected_matrix_actual :
    submatrix (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      submatrix (fromTable upperNineTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryNineSelectedInt
  change submatrix (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) id chargedInjection = _
  have h := third_nine_upper_actual_literal
  have hm := congrArg (fun T => fromTable T ordinaryFullFin nativeFin) h
  simp only [from_to_table] at hm
  rw [hm]

private theorem third_nine_lower_selected_matrix_actual :
    submatrix (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      submatrix (fromTable lowerNineTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryNineSelectedInt
  change submatrix (submatrix (sourceOrdinaryNineInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) id chargedInjection = _
  have h := third_nine_lower_actual_literal
  have hm := congrArg (fun T => fromTable T ordinaryFullFin nativeFin) h
  simp only [from_to_table] at hm
  rw [hm]

theorem third_nine_selected_actual :
    sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide) =
      nineSelectedStage03 := by
  apply matrix_int_eq_of_sum_submatrices
  · rw [third_nine_upper_selected_matrix_actual]
    rfl
  · rw [third_nine_lower_selected_matrix_actual]
    rfl

private theorem third_eleven_upper_selected_matrix_actual :
    submatrix (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id =
      submatrix (fromTable upperElevenTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryElevenSelectedInt
  change submatrix (submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inl id) id chargedInjection = _
  have h := third_eleven_upper_actual_literal
  have hm := congrArg (fun T => fromTable T ordinaryFullFin nativeFin) h
  simp only [from_to_table] at hm
  rw [hm]

private theorem third_eleven_lower_selected_matrix_actual :
    submatrix (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id =
      submatrix (fromTable lowerElevenTable ordinaryFullFin nativeFin) id chargedInjection := by
  unfold sourceOrdinaryElevenSelectedInt
  change submatrix (submatrix (sourceOrdinaryElevenInt (0 : Basis) (3 : Basis) (by decide)) Sum.inr id) id chargedInjection = _
  have h := third_eleven_lower_actual_literal
  have hm := congrArg (fun T => fromTable T ordinaryFullFin nativeFin) h
  simp only [from_to_table] at hm
  rw [hm]

theorem third_eleven_selected_actual :
    sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide) =
      elevenSelectedStage03 := by
  apply matrix_int_eq_of_sum_submatrices
  · rw [third_eleven_upper_selected_matrix_actual]
    rfl
  · rw [third_eleven_lower_selected_matrix_actual]
    rfl

private theorem third_nine_upper_weighted_matrix_actual :
    submatrix (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inl =
      fromTable upperNineWeightedTable pairFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (submatrix (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inl) pairFin ordinaryFullFin) pairFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_upper_weighted_actual_literal]

private theorem third_nine_lower_weighted_matrix_actual :
    submatrix (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inr =
      fromTable lowerNineWeightedTable pairFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (submatrix (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inr) pairFin ordinaryFullFin) pairFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_nine_lower_weighted_actual_literal]

theorem third_nine_weighted_actual :
    multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)) =
      nineWeightedStage03 := by
  apply matrix_int_eq_of_sum_columns
  · rw [third_nine_upper_weighted_matrix_actual]
    rfl
  · rw [third_nine_lower_weighted_matrix_actual]
    rfl

theorem third_nine_energy_actual_literal :
    toTable (multiply (multiply (adjoint (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)))
      (sourceOrdinaryNineSelectedInt (0 : Basis) (3 : Basis) (by decide))) pairFin pairFin =
      nineEnergyTable := by
  rw [third_nine_weighted_actual, third_nine_selected_actual]
  exact third_nineEnergy_staged_literal

private theorem third_eleven_upper_weighted_matrix_actual :
    submatrix (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inl =
      fromTable upperElevenWeightedTable pairFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (submatrix (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inl) pairFin ordinaryFullFin) pairFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_eleven_upper_weighted_actual_literal]

private theorem third_eleven_lower_weighted_matrix_actual :
    submatrix (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inr =
      fromTable lowerElevenWeightedTable pairFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (submatrix (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis))) id Sum.inr) pairFin ordinaryFullFin) pairFin ordinaryFullFin :=
      (from_to_table _ _ _).symm
    _ = _ := by rw [third_eleven_lower_weighted_actual_literal]

theorem third_eleven_weighted_actual :
    multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)) =
      elevenWeightedStage03 := by
  apply matrix_int_eq_of_sum_columns
  · rw [third_eleven_upper_weighted_matrix_actual]
    rfl
  · rw [third_eleven_lower_weighted_matrix_actual]
    rfl

theorem third_eleven_energy_actual_literal :
    toTable (multiply (multiply (adjoint (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide)))
      (sourceOrdinaryPCInt (0 : Basis) (3 : Basis)))
      (sourceOrdinaryElevenSelectedInt (0 : Basis) (3 : Basis) (by decide))) pairFin pairFin =
      elevenEnergyTable := by
  rw [third_eleven_weighted_actual, third_eleven_selected_actual]
  exact third_elevenEnergy_staged_literal

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
