import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.CoreNorm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem numeric_output_norm : ‖numericOutput‖ ≤ 2000000000 := by
  have same : ‖numericOutput‖=‖numericCoreInverse‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint numericFree) _
  rw [same]
  exact numeric_core_norm

theorem original_output_norm : ‖sourceOutputObservable loadTotalHamiltonian‖ ≤ 3000000000 := by
  have oldNorm : ‖calculatedOutputCore‖ ≤ 2000000000 := by
    have same : ‖calculatedOutputCore‖=‖numericCoreInverse‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint actualFree) _
    rw [same]
    exact numeric_core_norm
  have frame : ‖originalCalculatedOutput‖=‖sourceOutputObservable loadTotalHamiltonian‖ := by
    rw [original_calculated_output]
    exact StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) _
  have triangle := norm_sub_le_norm_sub_add_norm_sub originalCalculatedOutput calculatedOutputCore 0
  simp only [sub_zero] at triangle
  rw [frame] at triangle
  linarith [original_output_finite_error]

theorem original_frame_numeric_norm : ‖originalFrameNumericOutput‖ ≤ 2000000000 := by
  have same : ‖originalFrameNumericOutput‖=‖numericOutput‖ := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint (star installedLoadFrame)) _
  rw [same]
  exact numeric_output_norm

theorem effect_gap_of_norm (A : LoadedJoint) (paid : ‖A‖ ≤ 3000000000) :
    (1/10^10 : ℝ) ≤ effectGap A := by
  unfold effectGap
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (mul_pos (by norm_num) (measurementScale_pos A))).mpr
  unfold measurementScale
  linarith

theorem original_both_gap : (1/10^10 : ℝ) ≤ effectGap (sourceOutputObservable loadTotalHamiltonian) ∧
    (1/10^10 : ℝ) ≤ effectGap originalFrameNumericOutput :=
  ⟨effect_gap_of_norm _ original_output_norm,effect_gap_of_norm _ (original_frame_numeric_norm.trans (by norm_num))⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
