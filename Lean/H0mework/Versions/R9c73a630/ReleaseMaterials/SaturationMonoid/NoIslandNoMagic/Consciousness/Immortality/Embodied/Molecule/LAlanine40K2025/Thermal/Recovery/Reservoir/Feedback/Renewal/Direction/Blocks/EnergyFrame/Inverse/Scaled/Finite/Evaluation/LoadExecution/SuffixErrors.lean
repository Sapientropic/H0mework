import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution.ActionErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

attribute [local irreducible] PCExecution.pointerLoad PCExecution.pointerSupply PCExecution.pointerWeak pointerLoad pointerSupply pointerWeak

theorem nine_error : ‖PCExecution.nine-nine‖ ≤ (5/10^22 : ℝ) := by
  have first : ‖PCExecution.pointerLoad*PCExecution.pointerSupply-pointerLoad*pointerSupply‖ ≤ (9/10^23 : ℝ) :=
    (PCExecution.product_change PCExecution.pointerLoad PCExecution.pointerSupply pointerLoad pointerSupply).trans
      ((add_le_add (mul_le_mul pointer_load_error PCExecution.pointer_supply_norm (norm_nonneg _) (by norm_num))
        (mul_le_mul pointer_load_norm pointer_supply_error (norm_nonneg _) (by norm_num))).trans (by norm_num))
  have middle : ‖pointerLoad*pointerSupply‖ ≤ 16 :=
    (norm_mul_le pointerLoad pointerSupply).trans ((mul_le_mul pointer_load_norm pointer_supply_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (PCExecution.product_change (PCExecution.pointerLoad*PCExecution.pointerSupply) PCExecution.pointerSupply
    (pointerLoad*pointerSupply) pointerSupply).trans ((add_le_add
      (mul_le_mul first PCExecution.pointer_supply_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul middle pointer_supply_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem nine_norm : ‖nine‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.nine_norm nine_error).trans (by norm_num)

attribute [local irreducible] PCExecution.nine nine

theorem eleven_error : ‖PCExecution.eleven-eleven‖ ≤ (1/10^20 : ℝ) := by
  have first : ‖PCExecution.pointerLoad*PCExecution.pointerWeak-pointerLoad*pointerWeak‖ ≤ (9/10^23 : ℝ) :=
    (PCExecution.product_change PCExecution.pointerLoad PCExecution.pointerWeak pointerLoad pointerWeak).trans
      ((add_le_add (mul_le_mul pointer_load_error PCExecution.pointer_weak_norm (norm_nonneg _) (by norm_num))
        (mul_le_mul pointer_load_norm pointer_weak_error (norm_nonneg _) (by norm_num))).trans (by norm_num))
  have middle : ‖pointerLoad*pointerWeak‖ ≤ 16 :=
    (norm_mul_le pointerLoad pointerWeak).trans ((mul_le_mul pointer_load_norm pointer_weak_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (PCExecution.product_change (PCExecution.pointerLoad*PCExecution.pointerWeak) PCExecution.nine
    (pointerLoad*pointerWeak) nine).trans ((add_le_add
      (mul_le_mul first PCExecution.nine_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul middle nine_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem eleven_norm : ‖eleven‖ ≤ 4 :=
  (PCExecution.close_norm _ _ _ _ PCExecution.eleven_norm eleven_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
