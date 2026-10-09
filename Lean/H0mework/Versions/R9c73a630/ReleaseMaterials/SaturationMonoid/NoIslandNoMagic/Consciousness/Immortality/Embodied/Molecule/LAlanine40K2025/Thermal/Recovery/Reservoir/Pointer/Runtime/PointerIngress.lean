import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime.PointerAuthority

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Charging.Runtime
noncomputable section

def pointerOccurrencePresentation : ConstructivePresentation
    (reservoirLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt pointerParentVisit.current)
    (pointerLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      pointerLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => pointerEmitted .ingress
  backward := fun _ => pointerParentEvent.occurrence
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

theorem pointerTranslatedEntry_exact :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward pointerParentEntry = pointerInitialEntry :=
  pointerParentTranslation_entry

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
