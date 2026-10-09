import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Dynamics.ControlledPointerResponse

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback

open Collision Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

theorem respondNext_body (current : Live.State) :
    bodyRead (respondNext current).joint =
      Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) current.joint.toBlocks₁₁ +
        Quantum.conjugation (freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ))
          current.joint.toBlocks₂₂ := by
  rw [respondNext_joint]
  exact Readout.controlled_body_response _ _ _

theorem respondNext_observable (O : Current.FullJoint) (current : Live.State) :
    energy O (bodyRead (respondNext current).joint) =
      energy O (Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) current.joint.toBlocks₁₁) +
        energy O (Quantum.conjugation (freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ))
          current.joint.toBlocks₂₂) := by
  rw [respondNext_joint]
  exact Readout.controlled_expectation_sum _ _ _ _

theorem respondNext_cross (current : Live.State) :
    (respondNext current).joint.toBlocks₁₂ =
      (Current.loadPulse (nativeClockStep : ℝ) : Current.FullJoint) * current.joint.toBlocks₁₂ *
        star ((freePhase (nativeClockStep : ℝ) • Current.pulse (nativeClockStep : ℝ)) : Current.FullJoint) := by
  rw [respondNext_joint]
  exact Readout.controlled_cross_block _ _ _

theorem firstState_memory :
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian (zeroRead firstState.joint) =
      energy Load.Source.loadTotalHamiltonian Source.received.joint := by
  rw [firstState, respondNext_zero, receivedState_joint]
  exact sourceTarget_memory

theorem nextState_memory :
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian (zeroRead (Live.loadNext firstState).joint) =
      energy Load.Source.loadTotalHamiltonian Source.received.joint := by
  rw [Live.loadNext_pointer_zero]
  exact firstState_memory

theorem sourceGeneratedPointerFeedback :
    type_of% feedbackHamiltonian_hermitian ∧
    (∀ time, type_of% (feedbackPulse_eq_exp time)) ∧
    type_of% receivedState_joint ∧ type_of% firstState_clock ∧ type_of% nextState_clock ∧
    type_of% (respondNext_body receivedState) ∧
    (∀ O, type_of% (respondNext_observable O receivedState)) ∧
    type_of% (respondNext_cross receivedState) ∧
    type_of% firstState_memory ∧ type_of% nextState_memory ∧
    type_of% firstState_not_reset ∧ type_of% nextState_not_reset ∧
    type_of% firstState_completeAccount ∧
    type_of% (responseWork_body receivedState) ∧
    type_of% (Live.entropyProduction_disposition firstState) :=
  ⟨feedbackHamiltonian_hermitian, feedbackPulse_eq_exp, receivedState_joint, firstState_clock, nextState_clock,
    respondNext_body receivedState, fun O => respondNext_observable O receivedState,
    respondNext_cross receivedState, firstState_memory, nextState_memory,
    firstState_not_reset, nextState_not_reset, firstState_completeAccount, responseWork_body receivedState,
    Live.entropyProduction_disposition firstState⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
