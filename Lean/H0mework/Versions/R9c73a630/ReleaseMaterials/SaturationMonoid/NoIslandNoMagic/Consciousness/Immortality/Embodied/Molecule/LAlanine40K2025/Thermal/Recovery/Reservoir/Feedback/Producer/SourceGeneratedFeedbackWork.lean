import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackCurrent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback

open Collision Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def controlEnergy (current : Live.State) : ℝ := energy feedbackHamiltonian current.joint
def switchInWork (current : Live.State) : ℝ := controlEnergy current - Live.baselineEnergy current
def switchOutWork (current : Live.State) : ℝ := Live.baselineEnergy current - controlEnergy current
def responseWork (current : Live.State) : ℝ := switchInWork current + switchOutWork (respondNext current)

theorem respondNext_controlEnergy (current : Live.State) :
    controlEnergy (respondNext current) = controlEnergy current := by
  rw [controlEnergy, respondNext_joint]
  exact feedbackControl_conserves (nativeClockStep : ℝ) current.joint

theorem responseWork_actual (current : Live.State) :
    responseWork current = Live.baselineEnergy (respondNext current) - Live.baselineEnergy current := by
  unfold responseWork switchInWork switchOutWork
  rw [respondNext_controlEnergy]
  ring

theorem respondNext_netAccount (current : Live.State) :
    (Live.freeEnergy (respondNext current) - Live.freeEnergy current) +
      (Live.entropyProduction (respondNext current) - Live.entropyProduction current) = responseWork current := by
  rw [responseWork_actual]
  linarith [Live.complete_account current, Live.complete_account (respondNext current)]

theorem responseWork_body (current : Live.State) :
    responseWork current =
      energy Physical.baselineHamiltonian (bodyRead (respondNext current).joint) -
        energy Physical.baselineHamiltonian (bodyRead current.joint) := by
  rw [responseWork_actual, Live.baselineEnergy_split, Live.baselineEnergy_split, respondNext_pointerEnergy]
  ring

theorem firstState_completeAccount :
    Live.entropyProduction firstState + Live.freeEnergy firstState =
      Live.entropyProduction Live.initial + Live.freeEnergy Live.initial +
        Live.measurementWork Live.initial + responseWork receivedState := by
  have measurement := Live.measureNext_net_account Live.initial
  have feedback := respondNext_netAccount receivedState
  change (Live.freeEnergy receivedState - Live.freeEnergy Live.initial) +
    (Live.entropyProduction receivedState - Live.entropyProduction Live.initial) = _ at measurement
  change (Live.freeEnergy firstState - Live.freeEnergy receivedState) +
    (Live.entropyProduction firstState - Live.entropyProduction receivedState) = _ at feedback
  linarith

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
