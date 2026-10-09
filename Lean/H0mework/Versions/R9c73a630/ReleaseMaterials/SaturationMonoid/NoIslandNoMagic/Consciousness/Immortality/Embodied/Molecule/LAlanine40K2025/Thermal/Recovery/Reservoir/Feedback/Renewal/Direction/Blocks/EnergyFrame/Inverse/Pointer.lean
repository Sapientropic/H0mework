import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Roots
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.InstrumentContinuation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Measurement
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def numericPointer : Matrix.unitaryGroup PointerIndex ℂ :=
  approximatedPointerUnitary originalFrameNumericOutput original_frame_numeric_hermitian

theorem original_numeric_pointer_error : ‖(sourceUnitary : PointerJoint)-(numericPointer : PointerJoint)‖ ≤
    (28/10^6 : ℝ) := by
  have ha := sourceOutputObservable_hermitian loadTotalHamiltonian loadTotalHamiltonian_hermitian
  have hb := original_frame_numeric_hermitian
  change ‖dilationMatrix sourceEffect-dilationMatrix (approximatedBodyEffect originalFrameNumericOutput)‖ ≤ _
  apply (pointer_dilation_error _ _).trans
  have first : ‖effectRoot sourceEffect-effectRoot (approximatedBodyEffect originalFrameNumericOutput)‖ ≤
      (14/10^6 : ℝ) :=
    (body_root_error _ _ (boundedEffect_positive _ ha) (boundedEffect_positive _ hb)).trans original_numeric_root_error
  have second : ‖complementRoot sourceEffect-complementRoot (approximatedBodyEffect originalFrameNumericOutput)‖ ≤
      (14/10^6 : ℝ) := by
    change ‖CFC.sqrt (1-Incidence.bodyObservable (boundedEffect _))-
      CFC.sqrt (1-Incidence.bodyObservable (boundedEffect originalFrameNumericOutput))‖ ≤ _
    rw [bodyObservable_complement,bodyObservable_complement]
    exact (body_root_error _ _ (boundedEffect_complement_positive _ ha)
      (boundedEffect_complement_positive _ hb)).trans original_numeric_complement_error
  linarith

/-- The original normalized joint is retained, with both pointer branches and their coherence. -/
theorem original_numeric_pointer_observable (O : PointerJoint) :
    |energy O sourceTarget-energy O (Quantum.conjugation numericPointer sourceInitial)| ≤
      (56/10^6 : ℝ)*‖O‖ := by
  rw [sourceTarget_generated]
  have paid := Exchange.unitary_observable_error O sourceInitial sourceInitial_positive sourceInitial_trace
    sourceUnitary numericPointer
  change |energy O (Quantum.conjugation sourceUnitary sourceInitial)-
    energy O (Quantum.conjugation numericPointer sourceInitial)| ≤ _ at paid
  exact paid.trans (by nlinarith [mul_le_mul_of_nonneg_left original_numeric_pointer_error (norm_nonneg O)])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
