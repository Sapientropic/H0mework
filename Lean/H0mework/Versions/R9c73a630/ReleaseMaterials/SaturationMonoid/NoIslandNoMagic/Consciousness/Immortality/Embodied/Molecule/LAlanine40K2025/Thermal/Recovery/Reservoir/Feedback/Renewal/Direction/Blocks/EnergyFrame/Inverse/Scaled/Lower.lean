import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Core

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem numeric_core_lower : (99999998 : ℝ) < ‖numericCoreInverse‖ := by
  have oldNorm : ‖calculatedOutputCore‖=‖numericCoreInverse‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint actualFree) _
  have actualNorm : ‖originalCalculatedOutput‖=‖sourceOutputObservable loadTotalHamiltonian‖ := by
    rw [original_calculated_output]
    exact StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame) _
  have bound := norm_sub_le_norm_sub_add_norm_sub originalCalculatedOutput calculatedOutputCore 0
  simp only [sub_zero] at bound
  rw [oldNorm,actualNorm] at bound
  have lower := original_measurement_scale_lower
  unfold measurementScale at lower
  linarith [original_output_finite_error]

theorem scaled_core_lower : (17 : ℝ) < ‖core‖ := by
  rw [core_original,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos regularizer_positive]
  have lower : (1764/10^10 : ℝ) < regularizer := by
    unfold regularizer
    nlinarith [source_cos_lower]
  have paid := mul_lt_mul_of_pos_right lower (lt_trans (by norm_num) numeric_core_lower)
  have numeric := mul_lt_mul_of_pos_left numeric_core_lower (by norm_num : (0 : ℝ) < 1764/10^10)
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
