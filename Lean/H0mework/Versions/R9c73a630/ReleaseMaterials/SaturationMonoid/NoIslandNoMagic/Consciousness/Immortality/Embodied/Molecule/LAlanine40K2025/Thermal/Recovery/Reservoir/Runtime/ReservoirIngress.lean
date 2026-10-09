import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime.ReservoirAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Charging.Runtime
noncomputable section

def reservoirOccurrencePresentation : ConstructivePresentation
    (recoveryLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt chargingParentVisit.current)
    (reservoirLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      reservoirLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => reservoirEmitted .ingress
  backward := fun _ => chargingParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change RecoveryEventAt recoveryRuntimeAfterFirst.state.current support at event
    cases event.supportExact
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PLift (support = reservoirSupport) at event
    cases event.down
    rfl

theorem reservoirTranslatedEntry_exact :
    (chargingTranslation.oldOpenLedger chargingSourceSupport).forward chargingParentEntry = reservoirInitialEntry := by
  rw [chargingParentEntry_exact]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
