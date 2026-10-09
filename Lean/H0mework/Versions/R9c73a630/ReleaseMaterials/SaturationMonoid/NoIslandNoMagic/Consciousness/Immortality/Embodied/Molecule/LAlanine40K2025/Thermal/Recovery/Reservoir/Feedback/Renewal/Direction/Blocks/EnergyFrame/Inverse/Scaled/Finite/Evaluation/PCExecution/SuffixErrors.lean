import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.PointerErrors

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Propagation.Interface Load.Source Collision
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem old_pointer_load_norm : ‖Post.pointerLoadPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm Post.calculatedPointerLoad _ _ Post.pointer_load_polynomial_error).trans (by norm_num)
theorem old_pointer_supply_norm : ‖Post.pointerFeedbackPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm Post.calculatedPointerFeedback _ _ Post.pointer_feedback_polynomial_error).trans (by norm_num)
theorem old_pointer_weak_norm : ‖Post.pointerWeakPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm Post.calculatedPointerWeak _ _ Post.pointer_weak_polynomial_error).trans (by norm_num)

theorem pointer_load_norm : ‖pointerLoad‖ ≤ 3 := (close_norm _ _ _ _ old_pointer_load_norm pointer_load_error).trans (by norm_num)
theorem pointer_supply_norm : ‖pointerSupply‖ ≤ 3 := (close_norm _ _ _ _ old_pointer_supply_norm pointer_supply_error).trans (by norm_num)
theorem pointer_weak_norm : ‖pointerWeak‖ ≤ 3 := (close_norm _ _ _ _ old_pointer_weak_norm pointer_weak_error).trans (by norm_num)

attribute [local irreducible] Post.pointerLoadPolynomial Post.pointerFeedbackPolynomial Post.pointerWeakPolynomial pointerLoad pointerSupply pointerWeak

theorem nine_error : ‖Post.ninePolynomial-nine‖ ≤ (4/10^21 : ℝ) := by
  have first : ‖Post.pointerLoadPolynomial*Post.pointerFeedbackPolynomial-pointerLoad*pointerSupply‖ ≤ (1/10^21 : ℝ) :=
    (product_change Post.pointerLoadPolynomial Post.pointerFeedbackPolynomial pointerLoad pointerSupply).trans ((add_le_add
      (mul_le_mul pointer_load_error old_pointer_supply_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul pointer_load_norm pointer_supply_error (norm_nonneg _) (by norm_num))).trans (by norm_num))
  have middle : ‖pointerLoad*pointerSupply‖ ≤ 9 :=
    (norm_mul_le pointerLoad pointerSupply).trans ((mul_le_mul pointer_load_norm pointer_supply_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (product_change (Post.pointerLoadPolynomial*Post.pointerFeedbackPolynomial) Post.pointerFeedbackPolynomial
    (pointerLoad*pointerSupply) pointerSupply).trans ((add_le_add
      (mul_le_mul first old_pointer_supply_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul middle pointer_supply_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem old_nine_norm : ‖Post.ninePolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm Post.calculatedNine _ _ Post.original_nine_polynomial_error).trans (by norm_num)
theorem nine_norm : ‖nine‖ ≤ 3 := (close_norm _ _ _ _ old_nine_norm nine_error).trans (by norm_num)

attribute [local irreducible] Post.ninePolynomial nine

theorem eleven_error : ‖Post.elevenPolynomial-eleven‖ ≤ (4/10^20 : ℝ) := by
  have first : ‖Post.pointerLoadPolynomial*Post.pointerWeakPolynomial-pointerLoad*pointerWeak‖ ≤ (1/10^21 : ℝ) :=
    (product_change Post.pointerLoadPolynomial Post.pointerWeakPolynomial pointerLoad pointerWeak).trans ((add_le_add
      (mul_le_mul pointer_load_error old_pointer_weak_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul pointer_load_norm pointer_weak_error (norm_nonneg _) (by norm_num))).trans (by norm_num))
  have middle : ‖pointerLoad*pointerWeak‖ ≤ 9 :=
    (norm_mul_le pointerLoad pointerWeak).trans ((mul_le_mul pointer_load_norm pointer_weak_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (product_change (Post.pointerLoadPolynomial*Post.pointerWeakPolynomial) Post.ninePolynomial
    (pointerLoad*pointerWeak) nine).trans ((add_le_add
      (mul_le_mul first old_nine_norm (norm_nonneg _) (by norm_num))
      (mul_le_mul middle nine_error (norm_nonneg _) (by norm_num))).trans (by norm_num))

theorem old_eleven_norm : ‖Post.elevenPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm Post.calculatedEleven _ _ Post.original_eleven_polynomial_error).trans (by norm_num)
theorem eleven_norm : ‖eleven‖ ≤ 3 := (close_norm _ _ _ _ old_eleven_norm eleven_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
