import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Runtime.ChargingAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime
noncomputable section

def chargingParentVisit : SourceNativeTemporalVisitAt recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  recoveryRuntimeAfterFirst.current.visit

def chargingParentEvent : ExactTemporalCausalRootEventAt recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot chargingParentVisit :=
  recoveryLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt chargingParentVisit

def chargingParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? recoveryLivingRoot
    recoveryInitialEntry recoveryRuntimeAfterFirst.state.history).get (by rfl)

def chargingParentEntry := chargingParentGeneratedAuthority.1

def chargingParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt recoveryLivingRoot
    chargingParentVisit chargingParentEntry := chargingParentGeneratedAuthority.2

/-- Only the local program changes; no second world or copied ledger is introduced. -/
def chargingTranslation : TypedSemanticWorldNetworkTranslationAt RecoveryN RecoveryN where
  support := { forward := id, backward := id, backward_forward := fun _ => rfl }
  anchor := { forward := id, backward := id, backward_forward := fun _ => rfl }
  incidence := { forward := id, backward := id, backward_forward := fun _ => rfl }
  lineage := { forward := id, backward := id, backward_forward := fun _ => rfl }
  responsibility := { forward := id, backward := id, backward_forward := fun _ => rfl }
  claim := { forward := id, backward := id, backward_forward := fun _ => rfl }
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun _ => { forward := id, backward := id, backward_forward := fun _ => rfl }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ evidence => evidence
  oldDispositionSurvives := fun _ _ receipt => receipt

def chargingSourceSupport : RecoverySupport := recoveryCurrentSupport recoveryRuntimeAfterFirst.state.current

theorem chargingIngress_no_fresh_rows (support : RecoverySupport) (entry : OpenResponsibilityAt RecoveryN support) :
    Nonempty (Sigma fun oldEntry : OpenResponsibilityAt RecoveryN support =>
      PLift ((chargingTranslation.oldOpenLedger support).forward oldEntry = entry)) := ⟨⟨entry, ⟨rfl⟩⟩⟩

def chargingOccurrencePresentation : ConstructivePresentation
    (recoveryLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt chargingParentVisit.current)
    (chargingLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      chargingLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => chargingEmitted .ingress
  backward := fun _ => chargingParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change RecoveryEventAt recoveryRuntimeAfterFirst.state.current support at event
    cases event.supportExact
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change RecoveryEventAt (.running (chargingCurrentState .ingress)) support at event
    cases event.supportExact
    rfl

theorem chargingParentEntry_exact : chargingParentEntry = recoveryEntry chargingSourceSupport :=
  recoveryEntry_unique chargingSourceSupport chargingParentEntry

theorem chargingTranslatedEntry_exact :
    (chargingTranslation.oldOpenLedger chargingSourceSupport).forward chargingParentEntry = chargingInitialEntry := by
  rw [chargingParentEntry_exact]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Charging.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
