import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Runtime.FeedbackAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Charging.Runtime Pointer.Runtime
noncomputable section

def feedbackOccurrencePresentation : ConstructivePresentation
    (pointerLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt feedbackParentVisit.current)
    (feedbackLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      feedbackLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => feedbackEmitted .ingress
  backward := fun _ => feedbackParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change PLift (support = reservoirSupport) at event
    cases event.down
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PLift (support = reservoirSupport) at event
    cases event.down
    rfl

theorem feedbackTranslatedEntry_exact :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward feedbackParentEntry = feedbackInitialEntry :=
  feedbackParentTranslation_entry

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
