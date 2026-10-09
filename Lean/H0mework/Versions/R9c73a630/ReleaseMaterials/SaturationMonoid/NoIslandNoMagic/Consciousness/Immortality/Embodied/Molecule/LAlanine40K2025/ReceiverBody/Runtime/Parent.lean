import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Action
import H0mework.Versions.AB.Chemistry.LAlanineReentry.RuntimeRuntimeConsumers

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

abbrev Parent := ControlRecovery.Runtime.livingRoot
def parentMaterial := ControlRecovery.Runtime.afterSecond
def parentVisit : SourceNativeTemporalVisitAt Parent.toAuthoritativeRoot.toLedgerRoot :=
  parentMaterial.current.visit
def parentGenerated := Parent.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit parentVisit
def parentEvent : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit :=
  Parent.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt parentVisit

def parentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Parent
    ControlRecovery.Runtime.initialEntry parentMaterial.state.history).get (by rfl)
def parentEntry := parentGeneratedAuthority.1
def parentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Parent parentVisit parentEntry :=
  parentGeneratedAuthority.2
def parentEntryRow : parentGenerated.GeneratedEntryRowAt parentEntry :=
  (parentGenerated.canonicalGeneratedEntryRow? parentEntry).get (by rfl)

theorem parent_entry_exact : parentEntry=recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport parentEntry

theorem actuation_input_is_parent :
    resourceBefore=ControlRecovery.Runtime.currentMaterial parentVisit.current := rfl

def parentFace (face : ControlRecovery.Runtime.Projection) :=
  ControlRecovery.Runtime.facade.readoutAt parentMaterial face

theorem parent_face_factorizes (face : ControlRecovery.Runtime.Projection) :
    type_of% (ControlRecovery.Runtime.face_factorizes parentMaterial face) :=
  ControlRecovery.Runtime.face_factorizes parentMaterial face

abbrev BodyParent := Reentry.Runtime.reentryLivingRoot
def bodyMaterial := Reentry.Runtime.reentryRuntimeAfterFirst
def bodyVisit : SourceNativeTemporalVisitAt BodyParent.toAuthoritativeRoot.toLedgerRoot :=
  bodyMaterial.current.visit
def bodyEvent : ExactTemporalCausalRootEventAt BodyParent.toAuthoritativeRoot.toLedgerRoot bodyVisit :=
  BodyParent.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt bodyVisit

def bodyResponse := Reentry.Runtime.reentryResponse bodyMaterial.state.current
def bodyReceipt := Reentry.Runtime.generatedReentryAction_receipt

theorem body_response_original : bodyResponse=Reentry.Runtime.reentrySourceResult := by
  exact Reentry.Runtime.reentryRuntime_response bodyMaterial

theorem body_input_nuclear : bodyResponse.nuclear=Reentry.Source.stepReadout.nuclear := by
  rw [body_response_original]
  exact bodyReceipt.generatedNuclear

theorem body_input_held : bodyResponse.held=Reentry.Producer.exactTarget := by
  rw [body_response_original]
  exact bodyReceipt.exactHeld

theorem body_input_realized : bodyResponse.realized=Reentry.Source.targetRealized := by
  rw [body_response_original]
  exact bodyReceipt.numericalRealization

theorem body_face_factorizes (face : Reentry.Runtime.ReentryProjection) :
    type_of% (Reentry.Runtime.reentryRuntimeFace_factorizes bodyMaterial face) :=
  Reentry.Runtime.reentryRuntimeFace_factorizes bodyMaterial face

theorem body_occurrence_reads :
    type_of% (Reentry.Runtime.reentryRuntime_physical_installed Reentry.Runtime.reentryRuntimeSeed) :=
  Reentry.Runtime.reentryRuntime_physical_installed Reentry.Runtime.reentryRuntimeSeed

theorem input_clocks :
    (ControlRecovery.Runtime.readCurrent parentMaterial).quantum.localClock=18*Propagation.Producer.nativeClockStep ∧
      bodyResponse.clock=3*Propagation.Producer.nativeClockStep := by
  refine ⟨ControlRecovery.Runtime.actual_clocks.2.2,?_⟩
  rw [body_response_original]
  exact bodyReceipt.targetPhysicalClock

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Runtime
