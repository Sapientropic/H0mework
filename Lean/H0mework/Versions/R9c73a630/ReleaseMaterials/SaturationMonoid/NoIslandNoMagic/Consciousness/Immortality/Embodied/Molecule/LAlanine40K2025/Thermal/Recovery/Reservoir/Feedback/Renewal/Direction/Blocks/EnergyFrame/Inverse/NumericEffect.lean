import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Hermitian

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] actualFree numericFree numericCoreInverse calculatedOutputCore

def numericOutput : LoadedJoint := Quantum.conjugation numericFree numericCoreInverse

theorem numeric_output_hermitian : numericOutput.IsHermitian := by
  unfold numericOutput
  rw [Quantum.conjugation_apply]
  exact Matrix.isHermitian_mul_mul_conjTranspose _ numeric_core_hermitian

theorem numeric_effect_norm : ‖boundedEffect numericCoreInverse‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (boundedEffect_positive _ numeric_core_hermitian).nonneg).mpr
    (sub_nonneg.mp (boundedEffect_complement_positive _ numeric_core_hermitian).nonneg)

theorem numeric_free_effect_error : ‖boundedEffect calculatedOutputCore-boundedEffect numericOutput‖ ≤ (11/10^14 : ℝ) := by
  unfold calculatedOutputCore numericOutput
  rw [← bounded_effect_conjugation,← bounded_effect_conjugation]
  have bound := conjugation_action_error actualFree numericFree (boundedEffect numericCoreInverse)
  have cost := actual_numeric_free_error
  have h := mul_le_mul cost numeric_effect_norm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 55/10^15)
  exact bound.trans (by nlinarith)

theorem original_numeric_effect_error :
    ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-boundedEffect numericOutput‖ ≤
      (261/10^12 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian))
    (boundedEffect calculatedOutputCore) (boundedEffect numericOutput)
  linarith [original_effect_finite_error,numeric_free_effect_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
