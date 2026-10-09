import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackProgram

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Propagation.Producer
noncomputable section

def feedbackProcessCurrent (visit : RootVisit feedbackLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨FeedbackV, feedbackLivingRoot, .finite visit⟩

def feedbackRuntimeProcess : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit feedbackLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := feedbackProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨FeedbackV, feedbackLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨FeedbackV, feedbackLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := feedbackLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def feedbackRuntimeFacade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := feedbackRuntimeProcess
  FaceAt := fun _ => FeedbackProjection
  componentAt := fun _ _ => feedbackProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def feedbackRuntimeSeed : LivingRuntimeState feedbackRuntimeProcess := feedbackRuntimeFacade.seed
def feedbackRuntimeAfterFirst : LivingRuntimeState feedbackRuntimeProcess := feedbackRuntimeSeed.tick.next

theorem feedbackRuntimeFirst_generated :
    feedbackCurrentState feedbackRuntimeAfterFirst.state.current = generatedFeedbackAction.answer := rfl

theorem feedbackRuntimeNext_joint (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    (feedbackCurrentState runtime.tick.next.state.current).joint =
      Quantum.conjugation (feedbackControlRead runtime.state.current).action (feedbackCurrentState runtime.state.current).joint := by
  exact (feedbackNext_joint runtime.state.current).trans
    (congrArg (fun U => Quantum.conjugation U (feedbackCurrentState runtime.state.current).joint)
      (feedbackControl_action runtime.state.current).symm)

theorem feedbackRuntime_next_is_load (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    feedbackCurrentState runtime.tick.next.tick.next.state.current =
      Live.loadNext (feedbackCurrentState runtime.tick.next.state.current) := rfl

theorem feedbackRuntime_nextClock (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    (feedbackCurrentState runtime.tick.next.state.current).localClock =
      (feedbackCurrentState runtime.state.current).localClock + nativeClockStep := feedbackNext_clock runtime.state.current

theorem feedbackRuntime_firstClock :
    (feedbackCurrentState feedbackRuntimeAfterFirst.state.current).localClock = 7 * nativeClockStep := firstState_clock

theorem feedbackRuntimeFace_factorizes (runtime : LivingRuntimeState feedbackRuntimeProcess) (projection : FeedbackProjection) :
    type_of% (feedbackRuntimeFacade.readoutAt_factorizes runtime projection) :=
  feedbackRuntimeFacade.readoutAt_factorizes runtime projection

theorem feedbackRuntime_face_is_installed (runtime : LivingRuntimeState feedbackRuntimeProcess) (projection : FeedbackProjection) :
    feedbackRuntimeFacade.readoutAt runtime projection =
      feedbackProjectionLaw.outcomeAt projection (feedbackEmitted runtime.state.current) := rfl

theorem feedbackRuntime_wholeLedger_is_installed (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    feedbackRuntimeFacade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, feedbackLedgerCompiler.compile (feedbackEmitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt feedbackProjectionLaw .wholeLedger (feedbackEmitted runtime.state.current)) := rfl

theorem feedbackRuntime_netAccount_is_installed (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    feedbackRuntimeFacade.readoutAt runtime .netAccount =
      (.inl ⟨PUnit.unit, (feedbackEventWork runtime.state.current, feedbackAccumulatedWork runtime.state.current,
        ⟨feedbackNext_netAccount runtime.state.current⟩)⟩ :
        SourceNativeProjectionFiberAt feedbackProjectionLaw .netAccount (feedbackEmitted runtime.state.current)) := rfl

theorem feedbackRuntime_firstResponse_is_installed :
    feedbackRuntimeFacade.readoutAt feedbackRuntimeSeed .firstResponse =
      (.inl ⟨PUnit.unit, ⟨sourceGeneratedPointerFeedback, Resource.sourceGeneratedFeedbackResources,
        SourceGeneratedBodyEnsemble.source_mixture,
        (fun index => ⟨SourceGeneratedBodyEnsemble.source_index_left index,
          SourceGeneratedBodyEnsemble.source_index_right index⟩),
        (fun value => ⟨SourceGeneratedBodyEnsemble.source_joint_left_value value,
          SourceGeneratedBodyEnsemble.source_joint_right_value value⟩),
        SourceGeneratedBodyEnsemble.source_defect_conditional,
        SourceGeneratedBodyEnsemble.ValueCoarsening.original_joint_coarsens_index,
        SourceGeneratedBodyEnsemble.ValueCoarsening.value_information_le_index,
        SourceGeneratedBodyEnsemble.ValueCoarsening.value_information_loss_entropy,
        SourceGeneratedBodyEnsemble.original_marginal_as_body_diagonal,
        SourceGeneratedBodyEnsemble.value_information_quantum_gap,
        SourceGeneratedBodyEnsemble.holevoInformationLoss_nonnegative,
        SourceGeneratedBodyEnsemble.original_holevo_residual_account,
        FullGammaCross.received_cross_eq,
        FullGammaCross.received_cross_nonzero,
        FullGammaCross.first_cross_nonzero,
        SourceGeneratedBodyEnsemble.originalBlockQuantumInformation_eq_holevo,
        SourceGeneratedBodyEnsemble.originalFullQuantumInformation_coherence,
        SourceGeneratedBodyEnsemble.originalFullQuantumInformation_account⟩⟩ :
        SourceNativeProjectionFiberAt feedbackProjectionLaw .firstResponse (feedbackEmitted .ingress)) := rfl

theorem feedbackRuntime_nextResponse_is_inactive (runtime : LivingRuntimeState feedbackRuntimeProcess) :
    feedbackRuntimeFacade.readoutAt runtime.tick.next .firstResponse =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt feedbackProjectionLaw .firstResponse
        (feedbackEmitted runtime.tick.next.state.current)) := rfl

theorem feedbackRuntime_responseCertificate :
    type_of% (feedbackRuntimeFace_factorizes feedbackRuntimeSeed .firstResponse) ∧
      type_of% sourceGeneratedPointerFeedback := by
  refine ⟨feedbackRuntimeFace_factorizes feedbackRuntimeSeed .firstResponse, ?_⟩
  rcases feedbackRuntimeFacade.readoutAt feedbackRuntimeSeed .firstResponse with ⟨_, delivered⟩ | inactive
  · exact delivered.down.1
  · exact PEmpty.elim inactive

theorem feedbackRuntime_memory :
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian
      (zeroRead (feedbackCurrentState feedbackRuntimeAfterFirst.state.current).joint) =
        Collision.energy Load.Source.loadTotalHamiltonian Source.received.joint := by
  rcases feedbackRuntime_responseCertificate.2 with ⟨_, _, _, _, _, _, _, _, memory, _⟩
  exact memory

theorem feedbackRuntime_response :
    type_of% (respondNext_body receivedState) := by
  rcases feedbackRuntime_responseCertificate.2 with ⟨_, _, _, _, _, response, _⟩
  exact response

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
