import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPulses.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

private theorem first_pulse_norm (P : PointerJoint)
    (kept : Preserves Sectors.pointerOrbit P) (bound : ‖P‖ ≤ (4 : ℝ)) :
    ‖(restrict Sectors.pointerOrbit (donorSector (s((0 : Basis),1))) P).submatrix
      (coordinatePointer (s((0 : Basis),1)) (ordinaryFullEquiv (0 : Basis) 1 (by decide)))
      (coordinatePointer (s((0 : Basis),1)) (ordinaryFullEquiv (0 : Basis) 1 (by decide)))‖ ≤
      (4 : ℝ) := by
  rw [Finite.reindex_norm]
  exact ((norm_le_iff_block_norm_le kept 4 (by norm_num)).mp bound) _

theorem source_first_load_pulse_norm :
    ‖qvalue (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (4 : ℝ) := by
  rw [ordinary_pointer_load_value]
  exact first_pulse_norm LoadExecution.pointerLoad pointer_load_preserves
    LoadExecution.pointer_load_norm

theorem source_first_supply_pulse_norm :
    ‖qvalue (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (4 : ℝ) := by
  rw [ordinary_pointer_supply_value]
  exact first_pulse_norm LoadExecution.pointerSupply pointer_supply_preserves
    LoadExecution.pointer_supply_norm

theorem source_first_weak_pulse_norm :
    ‖qvalue (ordinaryPointerWeakQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (4 : ℝ) := by
  rw [ordinary_pointer_weak_value]
  exact first_pulse_norm LoadExecution.pointerWeak pointer_weak_preserves
    LoadExecution.pointer_weak_norm

private theorem step_norm (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull))
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (n : ℝ) (pBound : ‖qvalue P‖ ≤ (4 : ℝ))
    (vBound : ‖qvalue V‖ ≤ n) :
    ‖qvalue (qmultiply P V)‖ ≤ 4*n := by
  rw [qvalue_multiply]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul pBound vBound (norm_nonneg _) (by norm_num))

theorem source_first_entrance_norm :
    ‖qvalue (ordinaryEntranceQ (0 : Basis) (1 : Basis) (by decide))‖ ≤
      (16800 : ℝ) := by
  rw [ordinaryEntranceQ,qvalue_multiply]
  have h := Matrix.l2_opNorm_mul
    (qvalue (ordinarySourceColumnsQ (0 : Basis) (1 : Basis) (by decide)))
    (qvalue (ordinaryReceivedQ (0 : Basis) (1 : Basis) (by decide)))
  have product := mul_le_mul source_first_columns_norm source_first_received_norm
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 16700)
  exact h.trans (by nlinarith only [product])

theorem source_first_after_supply1_norm :
    ‖qvalue sourceFirstAfterSupply1Q‖ ≤ (67200 : ℝ) := by
  convert (step_norm _ _ 16800 source_first_supply_pulse_norm source_first_entrance_norm) using 1
  all_goals first | rfl | norm_num

theorem source_first_after_supply2_norm :
    ‖qvalue sourceFirstAfterSupply2Q‖ ≤ (268800 : ℝ) := by
  convert (step_norm _ _ 67200 source_first_supply_pulse_norm source_first_after_supply1_norm) using 1
  all_goals first | rfl | norm_num

theorem source_first_nine_norm :
    ‖qvalue sourceFirstNineQ‖ ≤ (1075200 : ℝ) := by
  convert (step_norm _ _ 268800 source_first_load_pulse_norm source_first_after_supply2_norm) using 1
  all_goals first | rfl | norm_num

theorem source_first_after_weak_norm :
    ‖qvalue sourceFirstAfterWeakQ‖ ≤ (4300800 : ℝ) := by
  convert (step_norm _ _ 1075200 source_first_weak_pulse_norm source_first_nine_norm) using 1
  all_goals first | rfl | norm_num

theorem source_first_eleven_norm :
    ‖qvalue sourceFirstElevenQ‖ ≤ (17203200 : ℝ) := by
  convert (step_norm _ _ 4300800 source_first_load_pulse_norm source_first_after_weak_norm) using 1
  all_goals first | rfl | norm_num


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
