import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadActionAuthority

/-! # The exact powered successor supplies the thermal-load action's causal ingress -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def loadParentVisit : SourceNativeTemporalVisitAt Powered.Runtime.poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  Powered.Runtime.poweredRuntimeAfterFirst.tick.next.current.visit

def loadParentEvent : ExactTemporalCausalRootEventAt
    Powered.Runtime.poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot loadParentVisit :=
  Powered.Runtime.poweredLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt loadParentVisit

def loadParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Powered.Runtime.poweredLivingRoot
    Powered.Runtime.poweredInitialEntry Powered.Runtime.poweredRuntimeAfterFirst.tick.next.state.history).get (by rfl)

def loadParentEntry := loadParentGeneratedAuthority.1

def loadParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Powered.Runtime.poweredLivingRoot
    loadParentVisit loadParentEntry := loadParentGeneratedAuthority.2

def loadOccurrencePresentation : ConstructivePresentation
    (Powered.Runtime.poweredLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt loadParentVisit.current)
    (loadLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      loadLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => loadEmitted .ingress
  backward := fun _ => loadParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change Powered.Runtime.PoweredEventAt Powered.Runtime.poweredRuntimeAfterFirst.tick.next.state.current support at event
    cases event.supportExact
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change LoadEventAt .ingress support at event
    cases event.supportExact
    rfl

theorem loadParentEntry_exact : loadParentEntry = Powered.Runtime.poweredEntry loadSourceSupport :=
  Powered.Runtime.poweredEntry_unique loadSourceSupport loadParentEntry

theorem loadTranslatedEntry_exact :
    (loadTranslation.oldOpenLedger loadSourceSupport).forward loadParentEntry = loadInitialEntry := by
  rw [loadParentEntry_exact]
  rfl

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
