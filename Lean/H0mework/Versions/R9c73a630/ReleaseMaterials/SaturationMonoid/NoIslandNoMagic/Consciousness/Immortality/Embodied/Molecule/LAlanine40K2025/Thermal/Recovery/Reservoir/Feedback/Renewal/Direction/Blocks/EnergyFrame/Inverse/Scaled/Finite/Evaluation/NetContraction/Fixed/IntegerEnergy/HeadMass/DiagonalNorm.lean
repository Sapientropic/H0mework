import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.DiagonalSource
set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Collision Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_diagonal_injection_injective : Function.Injective diagonalInjection := by
  intro i j h
  rcases i with ⟨p,e⟩
  rcases j with ⟨q,f⟩
  simp only [diagonalInjection,Prod.mk.injEq,Sum.inl.injEq] at h
  rcases h with ⟨⟨hp,_⟩,he⟩
  exact Prod.ext hp he

theorem source_diagonal_columns_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (sourceColumnsQ (s(a,a)) (diagonalFullEquiv a different)
      diagonalInjection)‖ ≤ (5 : ℝ) := by
  rw [sourceColumnsQ,qvalue_multiply,qvalue_submatrix,qvalue_submatrix,
    pointerBlockQ_value,supplyBlockQ_value]
  let full := diagonalFullEquiv a different
  let pointer := coordinatePointer (s(a,a)) full
  have rootNorm : ‖(localPointer (s(a,a))).submatrix pointer
      (fun i => pointer (.inl i))‖ ≤ (2001/1000 : ℝ) := by
    change ‖PCExecution.pointer.submatrix
      (fun i => (pointer i).val) (fun j => (pointer (.inl j)).val)‖ ≤ _
    have left : Function.Injective (fun i => (pointer i).val) := by
      intro i j h
      exact pointer.injective (Subtype.val_injective h)
    have right : Function.Injective (fun j => (pointer (.inl j)).val) := by
      intro i j h
      exact Sum.inl_injective (left h)
    exact (submatrix_norm_le PCExecution.pointer _ _ left right).trans
      source_pointer_norm_sharp
  have supplyNorm : ‖(localSupply (s(a,a))).submatrix full
      (fun i => full (diagonalInjection i))‖ ≤ (2001/1000 : ℝ) := by
    change ‖PCExecution.supply.submatrix (fun i => (full i).val)
      (fun j => (full (diagonalInjection j)).val)‖ ≤ _
    have left : Function.Injective (fun i => (full i).val) := by
      intro i j h
      exact full.injective (Subtype.val_injective h)
    have right : Function.Injective
        (fun j => (full (diagonalInjection j)).val) := by
      intro i j h
      exact source_diagonal_injection_injective (left h)
    exact (submatrix_norm_le PCExecution.supply _ _ left right).trans
      source_supply_norm_sharp
  have product := mul_le_mul rootNorm supplyNorm (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 2001/1000)
  exact (Matrix.l2_opNorm_mul _ _).trans (by nlinarith only [product])

theorem source_diagonal_received_norm (a : Basis) :
    ‖qvalue (sourceDiagonalReceivedQ a)‖ ≤ (1001/1000 : ℝ) := by
  rw [source_diagonal_received_value]
  have parent : ‖restrict pceOrbit (s(a,a)) LoadExecution.receivedWord‖ ≤
      (1001/1000 : ℝ) :=
    ((norm_le_iff_block_norm_le received_preserves (1001/1000) (by norm_num)).mp
      source_received_word_norm_sharp) (s(a,a))
  change ‖(restrict pceOrbit (s(a,a)) LoadExecution.receivedWord).submatrix
    (Scaled.Order.diagonalPCEEquiv a) (Scaled.Order.diagonalPCEEquiv a)‖ ≤ _
  rw [Finite.reindex_norm]
  exact parent

private theorem diagonal_pointer_address_injective (a : Basis) (different : a ≠ 97) :
    Function.Injective
      (fun i => (coordinatePointer (s(a,a)) (diagonalFullEquiv a different) i).val) := by
  intro i j h
  exact (coordinatePointer (s(a,a)) (diagonalFullEquiv a different)).injective
    (Subtype.val_injective h)

theorem source_diagonal_load_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (4 : ℝ) := by
  rw [coordinateLoadQ,qvalue_submatrix,Spec.pointerLoad_value]
  have inj := diagonal_pointer_address_injective a different
  exact (submatrix_norm_le LoadExecution.pointerLoad _ _ inj inj).trans
    LoadExecution.pointer_load_norm

theorem source_diagonal_supply_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (coordinateSupplyQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (4 : ℝ) := by
  rw [coordinateSupplyQ,qvalue_submatrix,Spec.pointerSupply_value]
  have inj := diagonal_pointer_address_injective a different
  exact (submatrix_norm_le LoadExecution.pointerSupply _ _ inj inj).trans
    LoadExecution.pointer_supply_norm

theorem source_diagonal_weak_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (coordinateWeakQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (4 : ℝ) := by
  rw [coordinateWeakQ,qvalue_submatrix,Spec.pointerWeak_value]
  have inj := diagonal_pointer_address_injective a different
  exact (submatrix_norm_le LoadExecution.pointerWeak _ _ inj inj).trans
    LoadExecution.pointer_weak_norm

theorem source_diagonal_pc_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (coordinatePCQ (s(a,a)) (diagonalFullEquiv a different))‖ ≤
      (89 : ℝ) := by
  rw [coordinatePCQ,qvalue_submatrix,Spec.pcObservable_value]
  have inj := diagonal_pointer_address_injective a different
  exact (submatrix_norm_le Post.finitePCObservable _ _ inj inj).trans
    Post.finite_PC_observable_norm

theorem source_diagonal_entrance_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (sourceDiagonalEntranceQ a different)‖ ≤ (6 : ℝ) := by
  rw [sourceDiagonalEntranceQ,entranceColumnsQ,qvalue_multiply]
  change ‖qvalue (sourceColumnsQ (s(a,a)) (diagonalFullEquiv a different)
    diagonalInjection) * qvalue (sourceDiagonalReceivedQ a)‖ ≤ _
  have product := mul_le_mul (source_diagonal_columns_norm a different)
    (source_diagonal_received_norm a) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 5)
  exact (Matrix.l2_opNorm_mul _ _).trans (by nlinarith only [product])

private theorem diagonal_step_norm
    (P : MatrixQ (DiagonalFull ⊕ DiagonalFull) (DiagonalFull ⊕ DiagonalFull))
    (V : MatrixQ (DiagonalFull ⊕ DiagonalFull) (Fin 2 × Fin 2))
    (n : ℝ) (pBound : ‖qvalue P‖ ≤ (4 : ℝ))
    (vBound : ‖qvalue V‖ ≤ n) :
    ‖qvalue (qmultiply P V)‖ ≤ 4*n := by
  rw [qvalue_multiply]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul pBound vBound (norm_nonneg _) (by norm_num))

theorem source_diagonal_after_supply1_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (sourceDiagonalAfterSupply1Q a different)‖ ≤ (24 : ℝ) := by
  convert diagonal_step_norm _ _ 6 (source_diagonal_supply_norm a different)
    (source_diagonal_entrance_norm a different) using 1
  all_goals first | rfl | norm_num

theorem source_diagonal_after_supply2_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (sourceDiagonalAfterSupply2Q a different)‖ ≤ (96 : ℝ) := by
  convert diagonal_step_norm _ _ 24 (source_diagonal_supply_norm a different)
    (source_diagonal_after_supply1_norm a different) using 1
  all_goals first | rfl | norm_num

theorem source_diagonal_nine_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (nineColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
      (diagonalFullEquiv a different) diagonalInjection)‖ ≤ (384 : ℝ) := by
  change ‖qvalue (qmultiply (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalAfterSupply2Q a different))‖ ≤ _
  convert diagonal_step_norm _ _ 96 (source_diagonal_load_norm a different)
    (source_diagonal_after_supply2_norm a different) using 1
  all_goals first | rfl | norm_num

theorem source_diagonal_after_weak_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (sourceDiagonalAfterWeakQ a different)‖ ≤ (1536 : ℝ) := by
  convert diagonal_step_norm _ _ 384 (source_diagonal_weak_norm a different)
    (source_diagonal_nine_norm a different) using 1
  all_goals first | rfl | norm_num

theorem source_diagonal_eleven_norm (a : Basis) (different : a ≠ 97) :
    ‖qvalue (elevenColumnsQ (s(a,a)) (Scaled.Order.diagonalPCEEquiv a)
      (diagonalFullEquiv a different) diagonalInjection)‖ ≤ (6144 : ℝ) := by
  change ‖qvalue (qmultiply (coordinateLoadQ (s(a,a)) (diagonalFullEquiv a different))
    (sourceDiagonalAfterWeakQ a different))‖ ≤ _
  convert diagonal_step_norm _ _ 1536 (source_diagonal_load_norm a different)
    (source_diagonal_after_weak_norm a different) using 1
  all_goals first | rfl | norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
