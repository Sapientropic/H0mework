import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformPulseSource
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_ordinary_load_pulse_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryPointerLoadQ a b ordered)‖ ≤ (4 : ℝ) := by
  rw [← ordinary_pointer_load_source,qvalue_submatrix,Spec.pointerLoad_value]
  have injective := source_ordinary_pointer_address_injective a b ordered
  exact (submatrix_norm_le LoadExecution.pointerLoad _ _ injective injective).trans
    LoadExecution.pointer_load_norm

theorem source_ordinary_supply_pulse_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryPointerSupplyQ a b ordered)‖ ≤ (4 : ℝ) := by
  rw [← ordinary_pointer_supply_source,qvalue_submatrix,Spec.pointerSupply_value]
  have injective := source_ordinary_pointer_address_injective a b ordered
  exact (submatrix_norm_le LoadExecution.pointerSupply _ _ injective injective).trans
    LoadExecution.pointer_supply_norm

theorem source_ordinary_weak_pulse_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryPointerWeakQ a b ordered)‖ ≤ (4 : ℝ) := by
  rw [← ordinary_pointer_weak_source,qvalue_submatrix,Spec.pointerWeak_value]
  have injective := source_ordinary_pointer_address_injective a b ordered
  exact (submatrix_norm_le LoadExecution.pointerWeak _ _ injective injective).trans
    LoadExecution.pointer_weak_norm

private theorem ordinary_step_norm
    (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull))
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (n : ℝ) (pBound : ‖qvalue P‖ ≤ (4 : ℝ))
    (vBound : ‖qvalue V‖ ≤ n) :
    ‖qvalue (qmultiply P V)‖ ≤ 4*n := by
  rw [qvalue_multiply]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul pBound vBound (norm_nonneg _) (by norm_num))

theorem source_ordinary_entrance_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryEntranceQ a b ordered)‖ ≤ (6 : ℝ) := by
  rw [ordinaryEntranceQ,qvalue_multiply]
  have h := Matrix.l2_opNorm_mul
    (qvalue (ordinarySourceColumnsQ a b ordered))
    (qvalue (ordinaryReceivedQ a b ordered))
  have product := mul_le_mul (source_ordinary_columns_norm a b ordered)
    (source_ordinary_received_norm a b ordered)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
  exact h.trans (by nlinarith only [product])

theorem source_ordinary_after_supply1_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (sourceOrdinaryAfterSupply1Q a b ordered)‖ ≤ (24 : ℝ) := by
  convert ordinary_step_norm _ _ 6 (source_ordinary_supply_pulse_norm a b ordered)
    (source_ordinary_entrance_norm a b ordered) using 1
  all_goals first | rfl | norm_num

theorem source_ordinary_after_supply2_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (sourceOrdinaryAfterSupply2Q a b ordered)‖ ≤ (96 : ℝ) := by
  convert ordinary_step_norm _ _ 24 (source_ordinary_supply_pulse_norm a b ordered)
    (source_ordinary_after_supply1_norm a b ordered) using 1
  all_goals first | rfl | norm_num

theorem source_ordinary_nine_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryNineColumnsQ a b ordered)‖ ≤ (384 : ℝ) := by
  change ‖qvalue (qmultiply (ordinaryPointerLoadQ a b ordered)
    (sourceOrdinaryAfterSupply2Q a b ordered))‖ ≤ _
  convert ordinary_step_norm _ _ 96 (source_ordinary_load_pulse_norm a b ordered)
    (source_ordinary_after_supply2_norm a b ordered) using 1
  all_goals first | rfl | norm_num

theorem source_ordinary_after_weak_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (sourceOrdinaryAfterWeakQ a b ordered)‖ ≤ (1536 : ℝ) := by
  convert ordinary_step_norm _ _ 384 (source_ordinary_weak_pulse_norm a b ordered)
    (source_ordinary_nine_norm a b ordered) using 1
  all_goals first | rfl | norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
