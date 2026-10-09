import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionAuthority

/-! # The exact first load visit supplies recovery's causal authority and entire ledger -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def recoveryParentVisit : SourceNativeTemporalVisitAt Load.Runtime.loadLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  Load.Runtime.loadRuntimeAfterFirst.current.visit

def recoveryParentEvent : ExactTemporalCausalRootEventAt
    Load.Runtime.loadLivingRoot.toAuthoritativeRoot.toLedgerRoot recoveryParentVisit :=
  Load.Runtime.loadLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt recoveryParentVisit

def recoveryParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Load.Runtime.loadLivingRoot
    Load.Runtime.loadInitialEntry Load.Runtime.loadRuntimeAfterFirst.state.history).get (by rfl)

def recoveryParentEntry := recoveryParentGeneratedAuthority.1

def recoveryParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Load.Runtime.loadLivingRoot
    recoveryParentVisit recoveryParentEntry := recoveryParentGeneratedAuthority.2

def recoveryOccurrencePresentation : ConstructivePresentation
    (Load.Runtime.loadLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt recoveryParentVisit.current)
    (recoveryLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      recoveryLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => recoveryEmitted .ingress
  backward := fun _ => recoveryParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change Load.Runtime.LoadEventAt Load.Runtime.loadRuntimeAfterFirst.state.current support at event
    cases event.supportExact
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change RecoveryEventAt .ingress support at event
    cases event.supportExact
    rfl

theorem recoveryParentEntry_exact : recoveryParentEntry = Load.Runtime.loadEntry recoverySourceSupport :=
  Load.Runtime.loadEntry_unique recoverySourceSupport recoveryParentEntry

theorem recoveryTranslatedEntry_exact :
    (recoveryTranslation.oldOpenLedger recoverySourceSupport).forward recoveryParentEntry = recoveryInitialEntry := by
  rw [recoveryParentEntry_exact]
  rfl

end

end LAlanine40K2025.Thermal.Recovery.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
