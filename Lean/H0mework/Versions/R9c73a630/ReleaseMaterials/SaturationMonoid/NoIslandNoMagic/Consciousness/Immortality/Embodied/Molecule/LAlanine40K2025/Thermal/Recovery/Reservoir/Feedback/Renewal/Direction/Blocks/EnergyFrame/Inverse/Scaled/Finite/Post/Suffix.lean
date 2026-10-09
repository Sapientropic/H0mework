import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Pointer

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def calculatedNine : Matrix.unitaryGroup PointerIndex ℂ := Actions.reframeUnitary pointerFrame afterInstrumentNine
def calculatedEleven : Matrix.unitaryGroup PointerIndex ℂ := Actions.reframeUnitary pointerFrame afterInstrumentEleven

def ninePolynomial : PointerJoint := pointerLoadPolynomial*pointerFeedbackPolynomial*pointerFeedbackPolynomial
def elevenPolynomial : PointerJoint := pointerLoadPolynomial*pointerWeakPolynomial*ninePolynomial

theorem original_nine_factors : calculatedNine=calculatedPointerLoad*calculatedPointerFeedback*calculatedPointerFeedback := by
  rw [calculatedNine,afterInstrumentNine,Actions.reframe_mul,Actions.reframe_mul]
  rfl

theorem original_eleven_factors : calculatedEleven=calculatedPointerLoad*calculatedPointerWeak*calculatedNine := by
  rw [calculatedEleven,afterInstrumentEleven,Actions.reframe_mul,Actions.reframe_mul]
  rfl

theorem original_nine_polynomial_error : ‖(calculatedNine : PointerJoint)-ninePolynomial‖ ≤ (4/10^13 : ℝ) := by
  have first := Input.approximated_product_error calculatedPointerLoad calculatedPointerFeedback pointerLoadPolynomial pointerFeedbackPolynomial
    (12/10^14) (12/10^14) pointer_load_polynomial_error pointer_feedback_polynomial_error
  have firstBound := first.trans (show (12/10^14 : ℝ)+(1+12/10^14)*(12/10^14) ≤ 25/10^14 by norm_num)
  have second := Input.approximated_product_error (calculatedPointerLoad*calculatedPointerFeedback) calculatedPointerFeedback
    (pointerLoadPolynomial*pointerFeedbackPolynomial) pointerFeedbackPolynomial (25/10^14) (12/10^14) firstBound pointer_feedback_polynomial_error
  rw [original_nine_factors]
  exact second.trans (by norm_num)

theorem original_eleven_polynomial_error : ‖(calculatedEleven : PointerJoint)-elevenPolynomial‖ ≤ (7/10^13 : ℝ) := by
  have first := Input.approximated_product_error calculatedPointerLoad calculatedPointerWeak pointerLoadPolynomial pointerWeakPolynomial
    (12/10^14) (12/10^14) pointer_load_polynomial_error pointer_weak_polynomial_error
  have firstBound := first.trans (show (12/10^14 : ℝ)+(1+12/10^14)*(12/10^14) ≤ 25/10^14 by norm_num)
  have second := Input.approximated_product_error (calculatedPointerLoad*calculatedPointerWeak) calculatedNine
    (pointerLoadPolynomial*pointerWeakPolynomial) ninePolynomial (25/10^14) (4/10^13) firstBound original_nine_polynomial_error
  rw [original_eleven_factors]
  exact second.trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
