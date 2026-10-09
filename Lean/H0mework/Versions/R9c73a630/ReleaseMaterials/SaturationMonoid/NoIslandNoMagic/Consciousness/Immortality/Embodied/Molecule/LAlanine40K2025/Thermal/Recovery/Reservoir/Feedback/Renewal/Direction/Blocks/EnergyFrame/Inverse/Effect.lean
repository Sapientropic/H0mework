import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scale

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] originalCalculatedOutput calculatedOutputCore actualFree actualCoreInverse numericCoreInverse

theorem original_output_finite_error : ‖originalCalculatedOutput-calculatedOutputCore‖ ≤ (26/1000 : ℝ) := by
  rw [original_calculated_output_core,calculatedOutputCore,← map_sub]
  have same : ‖Quantum.conjugation actualFree (actualCoreInverse-numericCoreInverse)‖ = ‖actualCoreInverse-numericCoreInverse‖ :=
    StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint actualFree) _
  rw [same]
  exact actual_core_finite_error

theorem original_effect_finite_error :
    ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-
      boundedEffect calculatedOutputCore‖ ≤ (26/10^11 : ℝ) := by
  rw [original_effect_calculated]
  have bound := bounded_effect_relative_error originalCalculatedOutput calculatedOutputCore
  have scale := original_measurement_scale_lower
  rw [← original_scale_calculated] at scale
  apply bound.trans
  apply (div_le_iff₀ (measurementScale_pos originalCalculatedOutput)).mpr
  nlinarith [original_output_finite_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
