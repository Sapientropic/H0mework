import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerRuntimeAccount

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Charging.Runtime Pointer.Runtime Propagation.Producer
noncomputable section

def feedbackParentVisit : SourceNativeTemporalVisitAt pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  pointerRuntimeAfterFirst.current.visit

def feedbackParentGenerated :=
  pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit feedbackParentVisit

def feedbackParentEvent :
    ExactTemporalCausalRootEventAt pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot feedbackParentVisit :=
  pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt feedbackParentVisit

def feedbackParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? pointerLivingRoot
    pointerInitialEntry pointerRuntimeAfterFirst.state.history).get (by rfl)

def feedbackParentEntry := feedbackParentGeneratedAuthority.1

def feedbackParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt pointerLivingRoot
    feedbackParentVisit feedbackParentEntry := feedbackParentGeneratedAuthority.2

def feedbackParentEntryRow : feedbackParentGenerated.GeneratedEntryRowAt feedbackParentEntry :=
  (feedbackParentGenerated.canonicalGeneratedEntryRow? feedbackParentEntry).get (by rfl)

theorem feedbackParentEntry_exact : feedbackParentEntry = recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport feedbackParentEntry

theorem feedbackParentEvent_exact :
    feedbackParentEvent.occurrence = pointerEmitted pointerRuntimeAfterFirst.state.current := rfl

theorem feedbackParent_support :
    pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      feedbackParentEvent.occurrence = reservoirSupport := rfl

/-- The identity translation consumes the actual measured target, not the earlier supply visit. -/
theorem feedbackParentTranslation_support :
    chargingTranslation.support.forward
      (pointerLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        feedbackParentEvent.occurrence) = reservoirSupport := rfl

theorem feedbackParentTranslation_entry :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward feedbackParentEntry =
      recoveryEntry reservoirSupport := by
  rw [feedbackParentEntry_exact]
  rfl

theorem feedbackParentTranslation_no_fresh (entry : OpenResponsibilityAt RecoveryN reservoirSupport) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt RecoveryN reservoirSupport =>
      PLift ((chargingTranslation.oldOpenLedger reservoirSupport).forward oldEntry = entry)) :=
  chargingIngress_no_fresh_rows reservoirSupport entry

theorem feedback_received_is_parent :
    Live.first = pointerCurrentState pointerRuntimeAfterFirst.state.current := rfl

theorem feedbackParent_clock :
    (pointerCurrentState feedbackParentVisit.current).localClock = 6 * nativeClockStep :=
  pointerRuntime_firstClock

theorem feedbackParent_joint :
    (pointerCurrentState feedbackParentVisit.current).joint = sourceTarget :=
  Live.first_joint

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
