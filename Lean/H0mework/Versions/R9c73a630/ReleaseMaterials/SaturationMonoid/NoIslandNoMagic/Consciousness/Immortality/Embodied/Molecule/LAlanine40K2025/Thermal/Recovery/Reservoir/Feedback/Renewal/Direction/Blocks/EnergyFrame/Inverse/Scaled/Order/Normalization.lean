import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Whole

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def fiveBlockEffect : LoadedJoint := ((1/2 : ℝ) : ℂ) • 1+
  ((1/(2*(rationalRegularizer+wholeNormBound)) : ℝ) : ℂ) • rationalCore

theorem rational_effect_five_blocks : scaledEffect rationalRegularizer rationalCore=fiveBlockEffect := by
  unfold scaledEffect fiveBlockEffect
  rw [original_whole_norm_exact]

theorem source_five_block_effect_error :
    ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-
      Quantum.conjugation numericFree fiveBlockEffect‖ ≤ (262/10^12 : ℝ) := by
  rw [← rational_effect_five_blocks]
  exact source_rational_effect_error

theorem five_block_scale_lower : (16 : ℝ) < rationalRegularizer+wholeNormBound := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub core rationalCore 0
  simp only [sub_zero] at triangle
  rw [original_whole_norm_exact] at triangle
  linarith [scaled_core_lower,rational_core_error,rational_regularizer_positive]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
