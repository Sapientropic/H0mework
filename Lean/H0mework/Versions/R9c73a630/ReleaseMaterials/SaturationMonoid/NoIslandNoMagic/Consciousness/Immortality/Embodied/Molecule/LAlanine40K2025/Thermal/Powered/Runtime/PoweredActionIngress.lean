import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Runtime.PoweredActionAuthority

/-! # The exact field successor supplies the finite-controller action's causal ingress -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def poweredParentVisit : SourceNativeTemporalVisitAt Work.Runtime.fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  Work.Runtime.fieldRuntimeAfterFirst.current.visit

def poweredParentEvent : ExactTemporalCausalRootEventAt
    Work.Runtime.fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot poweredParentVisit :=
  Work.Runtime.fieldLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt poweredParentVisit

def poweredParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Work.Runtime.fieldLivingRoot
    Work.Runtime.fieldInitialEntry Work.Runtime.fieldRuntimeAfterFirst.state.history).get (by rfl)

def poweredParentEntry := poweredParentGeneratedAuthority.1

def poweredParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Work.Runtime.fieldLivingRoot
    poweredParentVisit poweredParentEntry := poweredParentGeneratedAuthority.2

def poweredOccurrencePresentation : ConstructivePresentation
    (Work.Runtime.fieldLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt poweredParentVisit.current)
    (poweredLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      poweredLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => poweredEmitted .ingress
  backward := fun _ => poweredParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change Work.Runtime.FieldEventAt Work.Runtime.fieldRuntimeAfterFirst.state.current support at event
    cases event.supportExact
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change PoweredEventAt .ingress support at event
    cases event.supportExact
    rfl

theorem poweredParentEntry_exact : poweredParentEntry = Work.Runtime.fieldEntry poweredSourceSupport :=
  Work.Runtime.fieldEntry_unique poweredSourceSupport poweredParentEntry

theorem poweredTranslatedEntry_exact :
    (poweredTranslation.oldOpenLedger poweredSourceSupport).forward poweredParentEntry = poweredInitialEntry := by
  rw [poweredParentEntry_exact]
  rfl

end

end LAlanine40K2025.Thermal.Powered.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
