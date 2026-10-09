import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackLedger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackWork

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackResources

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open Propagation.Producer Pointer.Runtime
open scoped ComplexOrder
noncomputable section

def feedbackControlRead : FeedbackCurrent → PointerControlRead
  | .ingress => ⟨feedbackHamiltonian, feedbackPulse (nativeClockStep : ℝ), nativeClockStep,
      switchInWork receivedState, switchOutWork firstState⟩
  | .running _ => ⟨Pointer.baselineHamiltonian, Pointer.loadPulse (nativeClockStep : ℝ), nativeClockStep, 0, 0⟩

def feedbackEventWork : FeedbackCurrent → ℝ
  | .ingress => responseWork receivedState
  | .running _ => 0

def feedbackAccumulatedWork : FeedbackCurrent → ℝ
  | .ingress => 0
  | .running _ => responseWork receivedState

theorem feedbackControl_work (current : FeedbackCurrent) :
    (feedbackControlRead current).switchInWork + (feedbackControlRead current).switchOutWork = feedbackEventWork current := by
  cases current with
  | ingress => rfl
  | running _ => exact add_zero _

theorem feedbackControl_positive (current : FeedbackCurrent) : 0 < (feedbackControlRead current).duration := by
  cases current <;> exact nativeClockStep_positive

open scoped Matrix.Norms.L2Operator in
theorem feedbackControl_exponential (current : FeedbackCurrent) :
    ((feedbackControlRead current).action : PointerJoint) =
      NormedSpace.exp (((feedbackControlRead current).duration : ℝ) •
        (-Complex.I • (feedbackControlRead current).hamiltonian)) := by
  cases current with
  | ingress => exact feedbackPulse_eq_exp _
  | running _ => exact loadPulse_baseline _

theorem feedbackControl_action (current : FeedbackCurrent) : (feedbackControlRead current).action = feedbackAction current := by
  cases current <;> rfl

theorem feedbackNext_energyBalance (current : FeedbackCurrent) :
    Live.baselineEnergy (feedbackCurrentState (feedbackNext current)) -
      Live.baselineEnergy (feedbackCurrentState current) = feedbackEventWork current := by
  cases current with
  | ingress => exact (responseWork_actual receivedState).symm
  | running state => exact sub_eq_zero.mpr (Live.loadNext_preserves_baseline state)

theorem feedbackNext_netAccount (current : FeedbackCurrent) :
    (Live.freeEnergy (feedbackCurrentState (feedbackNext current)) - Live.freeEnergy (feedbackCurrentState current)) +
      (Live.entropyProduction (feedbackCurrentState (feedbackNext current)) -
        Live.entropyProduction (feedbackCurrentState current)) = feedbackEventWork current := by
  cases current with
  | ingress => exact respondNext_netAccount receivedState
  | running state => exact Live.loadNext_net_account state

theorem feedbackAccumulatedWork_next (current : FeedbackCurrent) :
    feedbackAccumulatedWork (feedbackNext current) = feedbackAccumulatedWork current + feedbackEventWork current := by
  cases current with
  | ingress => exact (zero_add _).symm
  | running _ => exact (add_zero _).symm


theorem feedbackNext_pointerEnergy (current : FeedbackCurrent) :
    pointerEnergy (feedbackCurrentState (feedbackNext current)).joint =
      pointerEnergy (feedbackCurrentState current).joint := by
  cases current with
  | ingress => exact respondNext_pointerEnergy receivedState
  | running state => exact Live.loadNext_pointer_energy state

theorem feedbackNext_resourceBalance (current : FeedbackCurrent) :
    (Resource.pcEnergyOf (bodyRead (feedbackCurrentState (feedbackNext current)).joint) -
      Resource.pcEnergyOf (bodyRead (feedbackCurrentState current).joint)) +
    (Resource.donorEnergyOf (bodyRead (feedbackCurrentState (feedbackNext current)).joint) -
      Resource.donorEnergyOf (bodyRead (feedbackCurrentState current).joint)) +
    (Resource.environmentEnergyOf (bodyRead (feedbackCurrentState (feedbackNext current)).joint) -
      Resource.environmentEnergyOf (bodyRead (feedbackCurrentState current).joint)) +
    (Resource.boundaryEnergyOf (bodyRead (feedbackCurrentState (feedbackNext current)).joint) -
      Resource.boundaryEnergyOf (bodyRead (feedbackCurrentState current).joint)) = feedbackEventWork current := by
  linarith [Resource.current_total (feedbackCurrentState current),
    Resource.current_total (feedbackCurrentState (feedbackNext current)),
    feedbackNext_energyBalance current, feedbackNext_pointerEnergy current]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
