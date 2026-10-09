import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerActuation
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirRuntime

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Charging.Runtime Propagation.Producer
noncomputable section

def pointerParentVisit : SourceNativeTemporalVisitAt reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  reservoirRuntimeAfterFirst.current.visit

def pointerParentGenerated :=
  reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit pointerParentVisit

def pointerParentEvent :
    ExactTemporalCausalRootEventAt reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot pointerParentVisit :=
  reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt pointerParentVisit

def pointerParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? reservoirLivingRoot
    reservoirInitialEntry reservoirRuntimeAfterFirst.state.history).get (by rfl)

def pointerParentEntry := pointerParentGeneratedAuthority.1

def pointerParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt reservoirLivingRoot
    pointerParentVisit pointerParentEntry := pointerParentGeneratedAuthority.2

def pointerParentEntryRow : pointerParentGenerated.GeneratedEntryRowAt pointerParentEntry :=
  (pointerParentGenerated.canonicalGeneratedEntryRow? pointerParentEntry).get (by rfl)

theorem pointerParentEntry_exact : pointerParentEntry = recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport pointerParentEntry

theorem pointerParentEvent_exact :
    pointerParentEvent.occurrence = reservoirEmitted reservoirRuntimeAfterFirst.state.current := rfl

theorem pointerParent_support :
    reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      pointerParentEvent.occurrence = reservoirSupport := rfl

/-- Identity translation applies to this actual Reservoir visit, not the older charging visit. -/
theorem pointerParentTranslation_support :
    chargingTranslation.support.forward
      (reservoirLivingRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        pointerParentEvent.occurrence) = reservoirSupport := rfl

theorem pointerParentTranslation_entry :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward pointerParentEntry =
      recoveryEntry reservoirSupport := by
  rw [pointerParentEntry_exact]
  rfl

theorem pointerParentTranslation_no_fresh (entry : OpenResponsibilityAt RecoveryN reservoirSupport) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt RecoveryN reservoirSupport =>
      PLift ((chargingTranslation.oldOpenLedger reservoirSupport).forward oldEntry = entry)) :=
  chargingIngress_no_fresh_rows reservoirSupport entry

theorem pointer_received_is_parent :
    received = reservoirCurrentState reservoirRuntimeAfterFirst.state.current := rfl

theorem pointerParent_clock :
    (reservoirCurrentState pointerParentVisit.current).localClock = 5 * nativeClockStep :=
  reservoirRuntime_firstClock

theorem pointerParent_prepared_joint :
    sourceInitial = prepared (reservoirCurrentState pointerParentVisit.current).joint := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
