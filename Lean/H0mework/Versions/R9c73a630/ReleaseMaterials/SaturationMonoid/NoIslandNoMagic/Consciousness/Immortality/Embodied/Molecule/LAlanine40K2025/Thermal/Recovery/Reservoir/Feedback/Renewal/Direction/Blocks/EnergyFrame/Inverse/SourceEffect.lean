import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.NumericEffect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def originalFrameNumericOutput : LoadedJoint := Quantum.conjugation (star installedLoadFrame) numericOutput

theorem original_frame_numeric_hermitian : originalFrameNumericOutput.IsHermitian := by
  rw [originalFrameNumericOutput,Quantum.conjugation_apply]
  exact Matrix.isHermitian_mul_mul_conjTranspose _ numeric_output_hermitian

theorem source_frame_effect_error : ‖sourceMeasurementEffect loadTotalHamiltonian-boundedEffect originalFrameNumericOutput‖ ≤
    (261/10^12 : ℝ) := by
  have norm : ‖sourceMeasurementEffect loadTotalHamiltonian-boundedEffect originalFrameNumericOutput‖ =
      ‖Quantum.conjugation installedLoadFrame (sourceMeasurementEffect loadTotalHamiltonian)-boundedEffect numericOutput‖ := by
    have h := StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ LoadedJoint installedLoadFrame)
      (sourceMeasurementEffect loadTotalHamiltonian-boundedEffect originalFrameNumericOutput)
    change ‖Quantum.conjugation installedLoadFrame (_-_)‖ = _ at h
    rw [map_sub,bounded_effect_conjugation] at h
    have same : Quantum.conjugation installedLoadFrame originalFrameNumericOutput=numericOutput := by
      rw [originalFrameNumericOutput,Environment.conjugation_comp]
      simp only [Unitary.mul_star_self,Quantum.conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]
    rw [same] at h
    exact h.symm
  rw [norm]
  exact original_numeric_effect_error

theorem source_body_effect_error : ‖sourceEffect-approximatedBodyEffect originalFrameNumericOutput‖ ≤ (261/10^12 : ℝ) := by
  change ‖Incidence.bodyObservable (sourceMeasurementEffect loadTotalHamiltonian)-
    Incidence.bodyObservable (boundedEffect originalFrameNumericOutput)‖ ≤ _
  rw [← bodyObservable_sub]
  exact (body_observable_norm _).trans source_frame_effect_error

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
