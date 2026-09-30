import H0mework.Chemistry.LAlanineWork.FieldActionAuthority

/-! # The exact old causal occurrence supplies the controlled action's entire ingress -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def fieldParentVisit : SourceNativeTemporalVisitAt Installation.root.toAuthoritativeRoot.toLedgerRoot :=
  fieldSourceRuntime.current.visit

def fieldParentEvent : ExactTemporalCausalRootEventAt
    Installation.root.toAuthoritativeRoot.toLedgerRoot fieldParentVisit :=
  Installation.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt fieldParentVisit

def fieldParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Installation.root
    (Root.entryAt .targetErasedDensityBCPCensusFrozen) fieldSourceRuntime.state.history).get (by rfl)

def fieldParentEntry := fieldParentGeneratedAuthority.1

def fieldParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Installation.root
    fieldParentVisit fieldParentEntry := fieldParentGeneratedAuthority.2

def fieldOccurrencePresentation : ConstructivePresentation
    (Installation.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt fieldParentVisit.current)
    (fieldLivingRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      fieldLivingRoot.toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun _ => fieldEmitted .ingress
  backward := fun _ => fieldParentEvent.occurrence
  backward_forward := by
    rintro ⟨support, event⟩
    change Root.LAlanineRootEventAt (.nativeElectronicCurrent fieldSourceTime) support at event
    cases event
    rfl
  forward_backward := by
    rintro ⟨support, event⟩
    change FieldEventAt .ingress support at event
    cases event.supportExact
    rfl

theorem fieldParentEntry_exact : fieldParentEntry = Root.entryAt (.nativeElectronicCurrent fieldSourceTime) :=
  Root.entryAt_unique fieldParentEntry

theorem fieldTranslatedEntry_exact :
    (fieldTranslation.oldOpenLedger (.nativeElectronicCurrent fieldSourceTime)).forward fieldParentEntry =
      fieldInitialEntry := by
  rw [fieldParentEntry_exact]
  rfl

end

end LAlanine40K2025.Thermal.Work.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
