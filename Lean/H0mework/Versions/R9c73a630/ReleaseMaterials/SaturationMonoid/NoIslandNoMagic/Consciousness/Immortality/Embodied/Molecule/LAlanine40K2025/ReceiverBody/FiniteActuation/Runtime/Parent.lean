import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Integrals

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

abbrev Parent := Coulomb.Runtime.livingRoot
def parentMaterial := Coulomb.Runtime.afterFirst
def parentVisit : SourceNativeTemporalVisitAt Parent.toAuthoritativeRoot.toLedgerRoot :=
  parentMaterial.current.visit
def parentGenerated := Parent.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit parentVisit
def parentEvent : ExactTemporalCausalRootEventAt Parent.toAuthoritativeRoot.toLedgerRoot parentVisit :=
  Parent.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt parentVisit

def parentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? Parent
    ReceiverBody.Runtime.initialEntry parentMaterial.state.history).get (by rfl)
def parentEntry := parentGeneratedAuthority.1
def parentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt Parent parentVisit parentEntry :=
  parentGeneratedAuthority.2
def parentEntryRow : parentGenerated.GeneratedEntryRowAt parentEntry :=
  (parentGenerated.canonicalGeneratedEntryRow? parentEntry).get (by rfl)

theorem parent_entry_exact : parentEntry=recoveryEntry reservoirSupport :=
  recoveryEntry_unique reservoirSupport parentEntry

theorem input_is_parent : FiniteActuation.input=
    Coulomb.Runtime.readMaterial parentMaterial Coulomb.Runtime.first_ready := rfl

def parentFace (face : Coulomb.Runtime.Face) := Coulomb.Runtime.facade.readoutAt parentMaterial face

theorem parent_face_factorizes (face : Coulomb.Runtime.Face) :
    type_of% (Coulomb.Runtime.face_factorizes parentMaterial face) :=
  Coulomb.Runtime.face_factorizes parentMaterial face

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
