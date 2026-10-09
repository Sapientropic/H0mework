import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Measurement
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Inverse.Actual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Measurement Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] installedLoadFrame sourceOutputObservable BodyKernel.bodyFree
  loadTotalHamiltonian Spectral.Projection.excitedIndex

def originalCalculatedOutput : LoadedJoint := Quantum.conjugation installedLoadFrame
  (BasisInverse.actualOutput loadTotalHamiltonian)

theorem original_calculated_output : originalCalculatedOutput =
    Quantum.conjugation installedLoadFrame (sourceOutputObservable loadTotalHamiltonian) := by
  rw [originalCalculatedOutput,BasisInverse.original_inverse_formula]

theorem original_calculated_hermitian : originalCalculatedOutput.IsHermitian := by
  rw [original_calculated_output,Quantum.conjugation_apply]
  exact Matrix.isHermitian_mul_mul_conjTranspose _
    (sourceOutputObservable_hermitian loadTotalHamiltonian loadTotalHamiltonian_hermitian)

theorem original_scale_calculated : measurementScale originalCalculatedOutput =
    measurementScale (sourceOutputObservable loadTotalHamiltonian) := by
  rw [original_calculated_output,measurement_scale_conjugation]

theorem original_effect_calculated :
    Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian) =
      boundedEffect originalCalculatedOutput := by
  rw [sourceMeasurementEffect,bounded_effect_conjugation,original_calculated_output]

theorem original_effect_root_calculated :
    Quantum.conjugation installedLoadFrame (effectRoot (sourceMeasurementEffect loadTotalHamiltonian)) =
      effectRoot (boundedEffect originalCalculatedOutput) := by
  rw [sourceMeasurementEffect,effect_root_conjugation installedLoadFrame _
    (sourceOutputObservable_hermitian loadTotalHamiltonian loadTotalHamiltonian_hermitian),original_calculated_output]

theorem original_complement_root_calculated :
    Quantum.conjugation installedLoadFrame (complementRoot (sourceMeasurementEffect loadTotalHamiltonian)) =
      complementRoot (boundedEffect originalCalculatedOutput) := by
  rw [sourceMeasurementEffect,complement_root_conjugation installedLoadFrame _
    (sourceOutputObservable_hermitian loadTotalHamiltonian loadTotalHamiltonian_hermitian),original_calculated_output]

/-- Original received-body source and channel are both kept through the common calculated frame. -/
theorem original_measurement_read (rho : LoadedJoint) :
    (originalCalculatedOutput*Quantum.conjugation installedLoadFrame (BodyKernel.sourceBodyChannel rho)).trace =
      (loadTotalHamiltonian*rho).trace := by
  rw [original_calculated_output,BasisInverse.conjugation_pair,sourceOutputObservable_read]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
