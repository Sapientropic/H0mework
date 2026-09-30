import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Grounding
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Restriction
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.World

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
noncomputable section

abbrev LivingHeader := Σ N : WorldRelationNetwork.{0}, Σ V : ConstructiveRoot.Vocabulary.{0}, SourceNativeLivingRootClosure N V

def headerOfWorld (world : Σ N : WorldRelationNetwork.{0}, SourceNativeLivingRootCurrentAt N) : LivingHeader :=
  ⟨world.1, world.2.V, world.2.root⟩

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {old : SourceNativeLivingRootCurrentAt N}
    {materials : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank}

def readHeader (p : MotherNativeCurrent.Restriction rank old materials) : LivingHeader :=
  headerOfWorld (MotherNativeCurrent.world p.presentation.authority.network p.read)

theorem readHeader_eq (p : MotherNativeCurrent.Restriction rank old materials) :
    readHeader p = ⟨N, old.V, old.root⟩ := by
  rw [readHeader, MotherNativeCurrent.world_eq, p.read_eq]
  rfl

def currentCoordinates (p : MotherNativeCurrent.Restriction rank old materials) : Coordinates (rank := rank) N :=
  coordinatesOfRoot (MotherArenaHigher.split rank materials.1).1 p.value.1
    (MotherHandoffSource.joint_root_formed materials.1 p.value p.formed) p.presentation.authority

def currentOccurrence (p : MotherNativeCurrent.Restriction rank old materials) (current : old.V.Current) :
    old.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank :=
  MotherAuthorityCoordinates.occurrence (MotherArenaHigher.split rank materials.1).1 p.value.1
    (MotherHandoffSource.joint_root_formed materials.1 p.value p.formed) p.presentation.authority current

abbrev HeaderCoordinates (rank : Ordinal.{0}) (header : LivingHeader) :=
  Coordinates (rank := rank) header.1 × (NewOccurrence header.2.2 ↪ MotherArenaHigher.Base rank)

variable {V : ConstructiveRoot.Vocabulary.{0}} {oldWorld : SourceNativeAuthoritativeRootClosure N V}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    {rooted : RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure}
    {NewN : WorldRelationNetwork.{0}} {NewV : ConstructiveRoot.Vocabulary.{0}}
    {newRoot : SourceNativeLivingRootClosure NewN NewV}

/-- The revised network, vocabulary and living root fields are taken from
this actual recovered header. Equality only transports their dependent codes. -/
def formOnHeader (header : LivingHeader) (same : header = ⟨NewN, NewV, newRoot⟩)
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (coordinates : HeaderCoordinates rank ⟨NewN, NewV, newRoot⟩)
    (material : MotherArenaHigher.Material rank) : Option (FieldGroundedTypedSemanticWorldNetworkRevisionAt rooted) :=
  let actualCoordinates := Eq.mp (congrArg (HeaderCoordinates rank) same.symm) coordinates
  formRevision header.2.2 oldCoordinates actualCoordinates.1 oldOccurrence actualCoordinates.2 material

theorem formOnHeader_eq (header : LivingHeader) (same : header = ⟨NewN, NewV, newRoot⟩)
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (coordinates : HeaderCoordinates rank ⟨NewN, NewV, newRoot⟩)
    (material : MotherArenaHigher.Material rank) :
    formOnHeader header same oldCoordinates oldOccurrence coordinates material =
      formRevision newRoot oldCoordinates coordinates.1 oldOccurrence coordinates.2 material := by
  cases same
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
