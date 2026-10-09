import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackRuntimeResources
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Source

/-! # Exact feedback occurrence whose retained resources enter renewal -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Charging.Runtime Feedback.Runtime
noncomputable section

def parentVisit : SourceNativeTemporalVisitAt feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  feedbackRuntimeAfterFirst.current.visit

def parentGenerated :=
  feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit parentVisit

def parentEvent : ExactTemporalCausalRootEventAt
    feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot parentVisit :=
  feedbackLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt parentVisit

def parentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? feedbackLivingRoot
    feedbackInitialEntry feedbackRuntimeAfterFirst.state.history).get (by rfl)

def parentEntry := parentGeneratedAuthority.1
def parentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt feedbackLivingRoot
    parentVisit parentEntry := parentGeneratedAuthority.2

def parentEntryRow : parentGenerated.GeneratedEntryRowAt parentEntry :=
  (parentGenerated.canonicalGeneratedEntryRow? parentEntry).get (by rfl)

theorem parent_entry_exact : parentEntry = recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport parentEntry

theorem received_is_parent :
    received = feedbackCurrentState feedbackRuntimeAfterFirst.state.current := rfl

theorem parent_translation_entry :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward parentEntry =
      recoveryEntry reservoirSupport := by
  rw [parent_entry_exact]
  rfl

/-- The same sealed parent retains its full instrument, feedback, resource, and history delivery. -/
def parentMaterial : LivingRuntimeState feedbackRuntimeProcess := feedbackRuntimeAfterFirst

theorem parent_resources :
    type_of% (feedbackRuntimeFace_factorizes parentMaterial .resources) ∧
      type_of% feedbackRuntime_sourceGeneratedFeedbackResources :=
  ⟨feedbackRuntimeFace_factorizes parentMaterial .resources,
    feedbackRuntime_sourceGeneratedFeedbackResources⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
