import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Blocks
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Weak

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem controlled_polynomial_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (W U V : Matrix.unitaryGroup ι ℂ) (phase : unitary ℂ) (scalar : ℂ) (A B : Matrix ι ι ℂ) (a b e : ℝ)
    (left : ‖(Actions.reframeUnitary W U : Matrix ι ι ℂ)-A‖ ≤ a)
    (right : ‖(Actions.reframeUnitary W V : Matrix ι ι ℂ)-B‖ ≤ b)
    (phaseError : ‖(phase : ℂ)-scalar‖ ≤ e) :
    ‖(Actions.reframeUnitary (blockUnitary W W) (blockUnitary U (phase • V)) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ)-
      Matrix.fromBlocks A 0 0 (scalar • B)‖ ≤ max a (b+(1+b)*e) := by
  rw [reframe_blocks,reframe_phase]
  apply (blocks_error _ _ _ _).trans
  exact max_le_max left (phase_matrix_error phase scalar (Actions.reframeUnitary W V) B b e right phaseError)

def pointerFrame : Matrix.unitaryGroup PointerIndex ℂ := blockUnitary Supply.installedFullFrame Supply.installedFullFrame

def pointerLoadPolynomial : PointerJoint := Matrix.fromBlocks fullLoadPolynomial 0 0 (Phase.pointerPhase • fullLoadPolynomial)
def pointerFeedbackPolynomial : PointerJoint := Matrix.fromBlocks fullLoadPolynomial 0 0 (Phase.pointerPhase • Supply.fullSupplyPolynomial)
def pointerWeakPolynomial : PointerJoint := Matrix.fromBlocks fullLoadPolynomial 0 0 (Phase.pointerPhase • fullWeakPolynomial)

def calculatedPointerLoad : Matrix.unitaryGroup PointerIndex ℂ := Actions.reframeUnitary pointerFrame (loadPulse (nativeClockStep : ℝ))
def calculatedPointerFeedback : Matrix.unitaryGroup PointerIndex ℂ := Actions.reframeUnitary pointerFrame (feedbackPulse (nativeClockStep : ℝ))
def calculatedPointerWeak : Matrix.unitaryGroup PointerIndex ℂ := Actions.reframeUnitary pointerFrame (Weak.pointerPulse (nativeClockStep : ℝ))

theorem pointer_load_polynomial_error :
    ‖(calculatedPointerLoad : PointerJoint)-pointerLoadPolynomial‖ ≤ (12/10^14 : ℝ) := by
  exact (controlled_polynomial_error Supply.installedFullFrame (Current.loadPulse (nativeClockStep : ℝ))
    (Current.loadPulse (nativeClockStep : ℝ)) (freePhase (nativeClockStep : ℝ)) Phase.pointerPhase
    fullLoadPolynomial fullLoadPolynomial (113/10^15) (113/10^15) (12/10^18)
    original_full_load_polynomial_error original_full_load_polynomial_error Phase.original_phase_error).trans (by norm_num)

theorem pointer_feedback_polynomial_error :
    ‖(calculatedPointerFeedback : PointerJoint)-pointerFeedbackPolynomial‖ ≤ (12/10^14 : ℝ) := by
  exact (controlled_polynomial_error Supply.installedFullFrame (Current.loadPulse (nativeClockStep : ℝ))
    (Current.pulse (nativeClockStep : ℝ)) (freePhase (nativeClockStep : ℝ)) Phase.pointerPhase
    fullLoadPolynomial Supply.fullSupplyPolynomial (113/10^15) (112/10^15) (12/10^18)
    original_full_load_polynomial_error Supply.original_supply_polynomial_error Phase.original_phase_error).trans (by norm_num)

theorem pointer_weak_polynomial_error :
    ‖(calculatedPointerWeak : PointerJoint)-pointerWeakPolynomial‖ ≤ (12/10^14 : ℝ) := by
  exact (controlled_polynomial_error Supply.installedFullFrame (Current.loadPulse (nativeClockStep : ℝ))
    (Weak.fullPulse (nativeClockStep : ℝ)) (freePhase (nativeClockStep : ℝ)) Phase.pointerPhase
    fullLoadPolynomial fullWeakPolynomial (113/10^15) (115/10^15) (12/10^18)
    original_full_load_polynomial_error original_weak_polynomial_error Phase.original_phase_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
