import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.SharpNet.Runtime.Consumers
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Thermal
set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Charging.Runtime
noncomputable section

abbrev Parent := SharpNet.Runtime.livingRoot
def parentMaterial := SharpNet.Runtime.afterSecond
def parentVisit : SourceNativeTemporalVisitAt Parent.toAuthoritativeRoot.toLedgerRoot :=
  parentMaterial.current.visit
def parentGenerated := Parent.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit parentVisit
def parentEvent : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit :=
  Parent.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt parentVisit

def parentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Parent
    Renewal.Runtime.initialEntry parentMaterial.state.history).get (by rfl)
def parentEntry := parentGeneratedAuthority.1
def parentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Parent parentVisit parentEntry :=
  parentGeneratedAuthority.2
def parentEntryRow : parentGenerated.GeneratedEntryRowAt parentEntry :=
  (parentGenerated.canonicalGeneratedEntryRow? parentEntry).get (by rfl)

theorem parent_entry_exact : parentEntry=recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport parentEntry
theorem origin_is_parent : origin=Renewal.Runtime.currentState parentVisit.current := rfl
theorem parent_translation_entry :
    (chargingTranslation.oldOpenLedger reservoirSupport).forward parentEntry=recoveryEntry reservoirSupport := by
  rw [parent_entry_exact]
  rfl

def parentFace (face : SharpNet.Runtime.Face) :=
  SharpNet.Runtime.facade.readoutAt parentMaterial face

theorem parent_face_factorizes (face : SharpNet.Runtime.Face) :
    type_of% (SharpNet.Runtime.face_factorizes parentMaterial face) :=
  SharpNet.Runtime.face_factorizes parentMaterial face

theorem parent_source : SharpNet.Runtime.InstalledSharpNet :=
  SharpNet.Runtime.sourceGeneratedPhysicalSharpNetNext

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
