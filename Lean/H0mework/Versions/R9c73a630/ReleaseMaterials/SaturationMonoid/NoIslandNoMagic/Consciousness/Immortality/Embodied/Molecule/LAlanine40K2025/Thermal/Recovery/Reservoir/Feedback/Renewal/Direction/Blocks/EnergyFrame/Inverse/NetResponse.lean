import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.WeakResponse

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def loadResponseCost : ℝ := ‖loadInteraction*numericLoadPC-numericLoadPC*loadInteraction‖+(252/10^12 : ℝ)
def exchangeResponseCost : ℝ := 2*‖Powered.Producer.poweredTotalHamiltonian‖

attribute [local irreducible] Sectors.pcObservable loadResponseCost exchangeResponseCost numericLoadPC loadInteraction Current.loadPulse Weak.fullPulse

theorem original_pointer_weak_response (time : ℝ) :
    ‖Quantum.conjugation (star (Weak.pointerPulse time)) Sectors.pointerPCObservable-Sectors.pointerPCObservable‖ ≤
      |time| * max loadResponseCost exchangeResponseCost := by
  have paid := block_observable_response (Current.loadPulse time) (freePhase time • Weak.fullPulse time) Sectors.pcObservable
  rw [star_smul,Resource.unitPhase_conjugation] at paid
  have left : ‖Quantum.conjugation (star (Current.loadPulse time)) Sectors.pcObservable-Sectors.pcObservable‖ ≤
      |time| * loadResponseCost := by
    unfold loadResponseCost
    exact original_body_load_response time
  have right : ‖Quantum.conjugation (star (Weak.fullPulse time)) Sectors.pcObservable-Sectors.pcObservable‖ ≤
      |time| * exchangeResponseCost := by
    have source := original_weak_body_response time
    unfold exchangeResponseCost
    nlinarith
  have bound : max ‖Quantum.conjugation (star (Current.loadPulse time)) Sectors.pcObservable-Sectors.pcObservable‖
      ‖Quantum.conjugation (star (Weak.fullPulse time)) Sectors.pcObservable-Sectors.pcObservable‖ ≤
      |time| * max loadResponseCost exchangeResponseCost := max_le
    (left.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg time)))
    (right.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg time)))
  have result := paid.trans bound
  unfold Weak.pointerPulse Sectors.pointerPCObservable
  unfold pointerDiagonal at result
  exact result

theorem original_net_PC_response : ‖gainObservable Sectors.pointerPCObservable‖ ≤
    (nativeClockStep : ℝ)*(loadResponseCost+max loadResponseCost exchangeResponseCost) := by
  apply (original_gain_two_pulse_bound Sectors.pointerPCObservable).trans
  have left := original_pointer_load_response (nativeClockStep : ℝ)
  have right := original_pointer_weak_response (nativeClockStep : ℝ)
  unfold loadResponseCost at right ⊢
  rw [abs_of_pos Load.Producer.StrictThermal.nativeClock_small.1] at left right
  nlinarith

theorem original_PC_gain_source_cost :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-
      (Resource.pcEnergyOf (bodyRead (approximatedEleven originalFrameNumericOutput original_frame_numeric_hermitian))-
       Resource.pcEnergyOf (bodyRead (approximatedNine originalFrameNumericOutput original_frame_numeric_hermitian)))| ≤
      (56/10^6 : ℝ)*(nativeClockStep : ℝ)*(loadResponseCost+max loadResponseCost exchangeResponseCost) := by
  exact original_PC_gain_instrument_error.trans (by nlinarith [original_net_PC_response])

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
