import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Source.SourceGeneratedPointerFeedbackHamiltonian
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerThermodynamics

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback

open Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

def receivedState : Live.State := Live.first

def respondNext (current : Live.State) : Live.State :=
  ⟨current.localClock + nativeClockStep, feedbackPulse (nativeClockStep : ℝ) * current.action⟩

def firstState : Live.State := respondNext receivedState

theorem respondNext_joint (current : Live.State) :
    (respondNext current).joint =
      Quantum.conjugation (feedbackPulse (nativeClockStep : ℝ)) current.joint :=
  (Environment.conjugation_comp _ current.action sourceInitial).symm

theorem receivedState_joint : receivedState.joint = sourceTarget := Live.first_joint
theorem receivedState_clock : receivedState.localClock = 6 * nativeClockStep := Live.first_clock

theorem firstState_clock : firstState.localClock = 7 * nativeClockStep := by
  change receivedState.localClock + nativeClockStep = _
  rw [receivedState_clock]
  ring

theorem nextState_clock : (Live.loadNext firstState).localClock = 8 * nativeClockStep := by
  rw [Live.loadNext_clock, firstState_clock]
  ring

theorem respondNext_zero (current : Live.State) :
    zeroRead (respondNext current).joint = zeroRead current.joint := by
  rw [respondNext_joint]
  exact blockUnitary_preserves_zeroRead _ _ _

theorem respondNext_one (current : Live.State) :
    oneRead (respondNext current).joint = oneRead current.joint := by
  rw [respondNext_joint]
  exact blockUnitary_preserves_oneRead _ _ _

theorem respondNext_pointerEnergy (current : Live.State) :
    pointerEnergy (respondNext current).joint = pointerEnergy current.joint := by
  unfold pointerEnergy
  rw [respondNext_one]

theorem firstState_not_reset : firstState.joint ≠ sourceInitial := by
  intro same
  have retained := respondNext_one receivedState
  change oneRead firstState.joint = oneRead receivedState.joint at retained
  rw [same, sourceInitial, prepared_one_read, receivedState_joint] at retained
  linarith [sourceTarget_one_positive]

theorem nextState_not_reset : (Live.loadNext firstState).joint ≠ sourceInitial := by
  intro same
  have retained := Live.loadNext_pointer_one firstState
  rw [same, sourceInitial, prepared_one_read] at retained
  have positive : 0 < oneRead firstState.joint := by
    rw [firstState, respondNext_one, receivedState_joint]
    exact sourceTarget_one_positive
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
