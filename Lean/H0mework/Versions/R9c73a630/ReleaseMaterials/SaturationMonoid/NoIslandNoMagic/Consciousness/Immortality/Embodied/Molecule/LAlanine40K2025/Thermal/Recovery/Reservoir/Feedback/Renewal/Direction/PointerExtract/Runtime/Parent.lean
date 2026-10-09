import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.Material

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

abbrev Parent := Extract.Runtime.livingRoot
def parentMaterial := Extract.Runtime.afterFirst
def parentVisit : SourceNativeTemporalVisitAt Parent.toAuthoritativeRoot.toLedgerRoot :=
  parentMaterial.current.visit
def parentGenerated := Parent.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit parentVisit
def parentEvent : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit :=
  Parent.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt parentVisit

def parentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Parent
    Extract.Runtime.initialEntry parentMaterial.state.history).get (by rfl)
def parentEntry := parentGeneratedAuthority.1
def parentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Parent parentVisit parentEntry :=
  parentGeneratedAuthority.2
def parentEntryRow : parentGenerated.GeneratedEntryRowAt parentEntry :=
  (parentGenerated.canonicalGeneratedEntryRow? parentEntry).get (by rfl)

theorem parent_entry_exact : parentEntry=recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport parentEntry
theorem origin_is_parent : sourceEntry.quantum=Extract.Runtime.currentState parentVisit.current := rfl

def parentFace (face : Extract.Runtime.Projection) :=
  Extract.Runtime.facade.readoutAt parentMaterial face

theorem parent_face_factorizes (face : Extract.Runtime.Projection) :
    type_of% (Extract.Runtime.face_factorizes parentMaterial face) :=
  Extract.Runtime.face_factorizes parentMaterial face



end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
