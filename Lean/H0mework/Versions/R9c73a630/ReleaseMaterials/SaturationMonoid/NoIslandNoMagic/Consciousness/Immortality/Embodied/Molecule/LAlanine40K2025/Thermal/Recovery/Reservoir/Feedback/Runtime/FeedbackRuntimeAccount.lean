import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackRuntime
import H0mework.Versions.R9c73a630.Foundation.Runtime.GeneratedContinuity

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def feedbackPaidBalance (state : feedbackRuntimeProcess.State) : Prop :=
  Live.entropyProduction (feedbackCurrentState state.current) + Live.freeEnergy (feedbackCurrentState state.current) =
    Live.entropyProduction receivedState + Live.freeEnergy receivedState + feedbackAccumulatedWork state.current

def feedbackAccountLaw : SourceNativeGeneratedInvariantLaw feedbackRuntimeProcess :=
  .create (fun state => PLift (feedbackPaidBalance state))
    ⟨(add_zero _).symm⟩
    (fun state previous => ⟨by
      change Live.entropyProduction (feedbackCurrentState (feedbackNext state.current)) +
        Live.freeEnergy (feedbackCurrentState (feedbackNext state.current)) =
        Live.entropyProduction receivedState + Live.freeEnergy receivedState +
          feedbackAccumulatedWork (feedbackNext state.current)
      have paid := previous.down
      change Live.entropyProduction (feedbackCurrentState state.current) +
        Live.freeEnergy (feedbackCurrentState state.current) =
        Live.entropyProduction receivedState + Live.freeEnergy receivedState + feedbackAccumulatedWork state.current at paid
      linarith [feedbackNext_netAccount state.current, feedbackAccumulatedWork_next state.current]⟩)

theorem feedbackRuntime_entropyPaid (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    feedbackPaidBalance runtime.state := by
  have paid (state : feedbackRuntimeProcess.State) (reachable : SourceNativeRuntimeReachableAt feedbackRuntimeProcess state) :
      feedbackPaidBalance state := by
    induction reachable with
    | initial => exact feedbackAccountLaw.initialAt.down
    | @step state _ previous => exact (feedbackAccountLaw.advanceAt state ⟨previous⟩).down
  exact paid runtime.state runtime.reachable

theorem feedbackRuntime_allFinitePaid (depth : Nat) :
    feedbackPaidBalance (feedbackRuntimeProcess.stateAfter depth) := (feedbackAccountLaw.generatedAt depth).down

theorem feedbackRuntime_completeAccount (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    (∀ projection, type_of% (feedbackRuntimeFace_factorizes runtime projection)) ∧
    (∀ projection, type_of% (feedbackRuntime_face_is_installed runtime projection)) ∧
    type_of% (feedbackRuntime_wholeLedger_is_installed runtime) ∧
    type_of% (feedbackRuntime_netAccount_is_installed runtime) ∧
    type_of% (feedbackRuntimeNext_joint runtime) ∧ type_of% (feedbackRuntime_next_is_load runtime) ∧
    type_of% (feedbackRuntime_entropyPaid runtime) ∧
    0 ≤ Live.entropyProduction (feedbackCurrentState runtime.state.current) :=
  ⟨feedbackRuntimeFace_factorizes runtime, feedbackRuntime_face_is_installed runtime,
    feedbackRuntime_wholeLedger_is_installed runtime, feedbackRuntime_netAccount_is_installed runtime,
    feedbackRuntimeNext_joint runtime, feedbackRuntime_next_is_load runtime, feedbackRuntime_entropyPaid runtime,
    Live.entropyProduction_nonnegative _⟩

theorem feedbackRuntime_sourceGeneratedPointerFeedback :
    type_of% (feedbackRuntime_completeAccount feedbackRuntimeSeed) ∧
    type_of% feedbackRuntime_firstResponse_is_installed ∧ type_of% feedbackRuntime_responseCertificate ∧
    type_of% feedbackRuntime_memory ∧ type_of% feedbackRuntime_response ∧
    type_of% feedbackRuntimeFirst_generated ∧ type_of% generatedFeedbackAction_next ∧
    type_of% feedback_received_is_parent ∧ type_of% feedbackParent_clock ∧ type_of% feedbackParent_joint ∧
    type_of% feedbackRuntime_firstClock ∧
    type_of% (feedbackRuntime_nextResponse_is_inactive feedbackRuntimeSeed) ∧
    (∀ depth, type_of% (feedbackRuntime_allFinitePaid depth)) :=
  ⟨feedbackRuntime_completeAccount feedbackRuntimeSeed, feedbackRuntime_firstResponse_is_installed,
    feedbackRuntime_responseCertificate, feedbackRuntime_memory, feedbackRuntime_response,
    feedbackRuntimeFirst_generated, generatedFeedbackAction_next, feedback_received_is_parent,
    feedbackParent_clock, feedbackParent_joint, feedbackRuntime_firstClock,
    feedbackRuntime_nextResponse_is_inactive feedbackRuntimeSeed, feedbackRuntime_allFinitePaid⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
