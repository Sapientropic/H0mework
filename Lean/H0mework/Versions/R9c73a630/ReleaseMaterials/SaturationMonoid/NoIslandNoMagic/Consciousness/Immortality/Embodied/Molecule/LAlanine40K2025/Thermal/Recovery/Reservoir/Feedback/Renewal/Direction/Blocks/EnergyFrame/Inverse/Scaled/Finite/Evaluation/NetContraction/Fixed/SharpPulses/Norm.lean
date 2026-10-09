import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpColumns.Consumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

private theorem sharp_step_norm (P : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull))
    (V : MatrixQ (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex)
    (n : ℝ) (pBound : ‖qvalue P‖ ≤ (4 : ℝ))
    (vBound : ‖qvalue V‖ ≤ n) :
    ‖qvalue (qmultiply P V)‖ ≤ 4*n := by
  rw [qvalue_multiply]
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul pBound vBound (norm_nonneg _) (by norm_num))

theorem source_first_after_supply1_norm_sharp :
    ‖qvalue sourceFirstAfterSupply1Q‖ ≤ (24 : ℝ) := by
  convert (sharp_step_norm _ _ 6 source_first_supply_pulse_norm
    source_first_entrance_norm_sharp) using 1
  all_goals first | rfl | norm_num

theorem source_first_after_supply2_norm_sharp :
    ‖qvalue sourceFirstAfterSupply2Q‖ ≤ (96 : ℝ) := by
  convert (sharp_step_norm _ _ 24 source_first_supply_pulse_norm
    source_first_after_supply1_norm_sharp) using 1
  all_goals first | rfl | norm_num

theorem source_first_nine_norm_sharp :
    ‖qvalue sourceFirstNineQ‖ ≤ (384 : ℝ) := by
  convert (sharp_step_norm _ _ 96 source_first_load_pulse_norm
    source_first_after_supply2_norm_sharp) using 1
  all_goals first | rfl | norm_num

theorem source_first_after_weak_norm_sharp :
    ‖qvalue sourceFirstAfterWeakQ‖ ≤ (1536 : ℝ) := by
  convert (sharp_step_norm _ _ 384 source_first_weak_pulse_norm
    source_first_nine_norm_sharp) using 1
  all_goals first | rfl | norm_num

theorem source_first_eleven_norm_sharp :
    ‖qvalue sourceFirstElevenQ‖ ≤ (6144 : ℝ) := by
  convert (sharp_step_norm _ _ 1536 source_first_load_pulse_norm
    source_first_after_weak_norm_sharp) using 1
  all_goals first | rfl | norm_num

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
