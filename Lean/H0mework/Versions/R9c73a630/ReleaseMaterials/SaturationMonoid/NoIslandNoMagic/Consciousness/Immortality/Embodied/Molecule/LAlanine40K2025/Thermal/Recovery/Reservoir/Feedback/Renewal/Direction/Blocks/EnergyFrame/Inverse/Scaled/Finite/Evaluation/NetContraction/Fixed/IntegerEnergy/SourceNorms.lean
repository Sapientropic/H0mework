import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.NumericGain
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_first_pc_norm :
    ‖qvalue (ordinaryPCPointerQ (0 : Basis) (1 : Basis))‖ ≤ (89 : ℝ) := by
  rw [← source_first_pc_original,qvalue_submatrix,Spec.pcObservable_value]
  exact (submatrix_norm_le Post.finitePCObservable _ _
    source_first_pointer_address_injective source_first_pointer_address_injective).trans
      Post.finite_PC_observable_norm

private theorem first_local_action_norm (P : PointerJoint)
    (kept : Preserves Sectors.pointerOrbit P) (bound : ‖P‖ ≤ (4 : ℝ)) :
    ‖(restrict Sectors.pointerOrbit (donorSector (s((0 : Basis),1))) P).submatrix
      (coordinatePointer (s((0 : Basis),1)) (ordinaryFullEquiv (0 : Basis) 1 (by decide)))
      (coordinatePointer (s((0 : Basis),1)) (ordinaryFullEquiv (0 : Basis) 1 (by decide)))‖ ≤
      (4 : ℝ) := by
  rw [Finite.reindex_norm]
  exact ((norm_le_iff_block_norm_le kept 4 (by norm_num)).mp bound) _

theorem source_first_nine_norm_24 : ‖qvalue sourceFirstNineQ‖ ≤ (24 : ℝ) := by
  rw [source_first_nine_q_original,
    ordinary_nine_columns_value (0 : Basis) (1 : Basis) (by decide)]
  let k := s((0 : Basis),1)
  let body := Scaled.Order.offDiagonalPCEEquiv (0 : Basis) 1 (by decide)
  let full := ordinaryFullEquiv (0 : Basis) 1 (by decide)
  have same : nineColumns k body full ordinaryInjection =
      ((localNine k).submatrix (coordinatePointer k full) (coordinatePointer k full)) *
        entranceColumns k body full ordinaryInjection := by
    rw [coordinate_nine]
    simp only [nineColumns,Matrix.mul_assoc]
  rw [same]
  have action : ‖(localNine k).submatrix (coordinatePointer k full)
      (coordinatePointer k full)‖ ≤ (4 : ℝ) :=
    first_local_action_norm LoadExecution.nine nine_preserves LoadExecution.nine_norm
  have entrance : ‖entranceColumns k body full ordinaryInjection‖ ≤ (6 : ℝ) := by
    rw [← ordinary_entrance_value (0 : Basis) (1 : Basis) (by decide)]
    exact source_first_entrance_norm_sharp
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul action entrance (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 4)).trans (by norm_num))

theorem source_first_eleven_norm_24 : ‖qvalue sourceFirstElevenQ‖ ≤ (24 : ℝ) := by
  rw [source_first_eleven_q_original,
    ordinary_eleven_columns_value (0 : Basis) (1 : Basis) (by decide)]
  let k := s((0 : Basis),1)
  let body := Scaled.Order.offDiagonalPCEEquiv (0 : Basis) 1 (by decide)
  let full := ordinaryFullEquiv (0 : Basis) 1 (by decide)
  have same : elevenColumns k body full ordinaryInjection =
      ((localEleven k).submatrix (coordinatePointer k full) (coordinatePointer k full)) *
        entranceColumns k body full ordinaryInjection := by
    rw [coordinate_eleven,coordinate_nine]
    simp only [elevenColumns,nineColumns,Matrix.mul_assoc]
  rw [same]
  have action : ‖(localEleven k).submatrix (coordinatePointer k full)
      (coordinatePointer k full)‖ ≤ (4 : ℝ) :=
    first_local_action_norm LoadExecution.eleven eleven_preserves LoadExecution.eleven_norm
  have entrance : ‖entranceColumns k body full ordinaryInjection‖ ≤ (6 : ℝ) := by
    rw [← ordinary_entrance_value (0 : Basis) (1 : Basis) (by decide)]
    exact source_first_entrance_norm_sharp
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul action entrance (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 4)).trans (by norm_num))

theorem charged_injection_injective : Function.Injective
    (chargedInjection : Fin 2 × Fin 2 → LoadPrimitive.NativeIndex) := by
  intro i j h
  rcases i with ⟨a,e⟩
  rcases j with ⟨b,f⟩
  simp only [chargedInjection,Prod.mk.injEq] at h
  rcases h with ⟨⟨hab,_⟩,hef⟩
  exact Prod.ext hab hef

theorem source_first_nine_selected_norm_24 :
    ‖qvalue ((sourceFirstNineQ).submatrix id chargedInjection)‖ ≤ (24 : ℝ) := by
  rw [qvalue_submatrix]
  exact (submatrix_columns_norm_le _ chargedInjection charged_injection_injective).trans
    source_first_nine_norm_24

theorem source_first_eleven_selected_norm_24 :
    ‖qvalue ((sourceFirstElevenQ).submatrix id chargedInjection)‖ ≤ (24 : ℝ) := by
  rw [qvalue_submatrix]
  exact (submatrix_columns_norm_le _ chargedInjection charged_injection_injective).trans
    source_first_eleven_norm_24

theorem first_pair_address_injective :
    Function.Injective (pairAddress (0 : Basis) (1 : Basis)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [pairAddress] at h ⊢

theorem source_first_body_norm_10 :
    ‖qvalue (qkron (ordinaryPairBlockQ (0 : Basis) (1 : Basis)) environmentQ)‖ ≤
      (10 : ℝ) := by
  rw [qvalue_kron,ordinary_pair_block_value,environmentQ_value]
  have pairNorm : ‖InputProducts.pair‖ ≤ (5 : ℝ) := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub InputProducts.pair
      Field.computedPair 0
    simp only [sub_zero] at triangle
    rw [norm_sub_rev] at triangle
    linarith only [triangle,InputProducts.pair_error,PCExecution.field_pair_norm]
  have blockNorm : ‖originalPairBlock (0 : Basis) (1 : Basis)‖ ≤ (5 : ℝ) := by
    rw [originalPairBlock]
    exact (submatrix_norm_le InputProducts.pair _ _
      first_pair_address_injective first_pair_address_injective).trans pairNorm
  exact (kronecker_norm_le _ _).trans
    ((mul_le_mul blockNorm Diagonal.finite_environment_norm (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 5)).trans (by norm_num))

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
