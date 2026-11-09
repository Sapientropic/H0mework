import H0mework.Versions.R2.Foundation.Inquiry.Protocol
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.QueryHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint

universe u

/-- A typed signed input read on the actual resident. The resident's own
projection law supplies both the active witness and the payload. -/
structure ReadAt
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (Payload : Type u) : Type (u + 1) where
  face : SourceNativeRootSemanticFaceAt root visit
  restriction_eq : face.Restriction = Payload

namespace ReadAt

variable {N M : WorldRelationNetwork.{u}} {V W : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {Payload : Type u}

def read (input : ReadAt root visit Payload) : Payload :=
  cast input.restriction_eq input.face.rootRead

/-- The projection depends on the emitted current. Two exact visits can
have the same emitter current and different causal histories. -/
def atSameCurrent (input : ReadAt root visit Payload)
    {atTarget : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (same : visit.current = atTarget.current) : ReadAt root atTarget Payload := by
  cases visit
  cases atTarget
  cases same
  exact ⟨⟨input.face.projection, input.face.active, input.face.classifier_eq⟩, input.restriction_eq⟩

theorem atSameCurrent_read (input : ReadAt root visit Payload)
    {atTarget : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (same : visit.current = atTarget.current) : (input.atSameCurrent same).read = input.read := by
  cases visit
  cases atTarget
  cases same
  rfl

def frozenLaw (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (base : SourceNativeLivingRootClosure M W) :
    SourceNativeProjectionLaw base.source.base.restructuringSource.toLedgerSource :=
  QueryHistory.freeze root.source.base.projectionLaw (root.emitted visit.current)
    base.source.base.restructuringSource.toLedgerSource

/-- Inherit the original lane with its exact active and classification
proofs. The frozen projection computes the original dependent read. -/
def freeze (input : ReadAt root visit Payload) (base : SourceNativeLivingRootClosure M W)
    (atTarget : SourceNativeTemporalVisitAt
      (base.withProjectionCoface (frozenLaw root visit base)).toAuthoritativeRoot.toLedgerRoot) :
    ReadAt (base.withProjectionCoface (frozenLaw root visit base)) atTarget Payload :=
  ⟨⟨.component input.face.projection, input.face.active, input.face.classifier_eq⟩, input.restriction_eq⟩

theorem freeze_read (input : ReadAt root visit Payload) (base : SourceNativeLivingRootClosure M W)
    (atTarget : SourceNativeTemporalVisitAt
      (base.withProjectionCoface (frozenLaw root visit base)).toAuthoritativeRoot.toLedgerRoot) :
    (input.freeze base atTarget).read = input.read :=
  rfl

/-- Install the inherited lane alongside a new material or semantic write
on the target source. -/
def freezeWrite (input : ReadAt root visit Payload) (base : SourceNativeLivingRootClosure M W)
    (component : SourceNativeProjectionLaw base.source.base.restructuringSource.toLedgerSource)
    (atTarget : SourceNativeTemporalVisitAt
      ((base.withProjectionCoface (frozenLaw root visit base)).withProjectionCoface component).toAuthoritativeRoot.toLedgerRoot) :
    ReadAt ((base.withProjectionCoface (frozenLaw root visit base)).withProjectionCoface component) atTarget Payload :=
  let carried := input.freeze base atTarget
  ⟨⟨.inherited carried.face.projection, carried.face.active, carried.face.classifier_eq⟩,
    carried.restriction_eq⟩

theorem freezeWrite_read (input : ReadAt root visit Payload) (base : SourceNativeLivingRootClosure M W)
    (component : SourceNativeProjectionLaw base.source.base.restructuringSource.toLedgerSource)
    (atTarget : SourceNativeTemporalVisitAt
      ((base.withProjectionCoface (frozenLaw root visit base)).withProjectionCoface component).toAuthoritativeRoot.toLedgerRoot) :
    (input.freezeWrite base component atTarget).read = input.read :=
  rfl

end ReadAt

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
