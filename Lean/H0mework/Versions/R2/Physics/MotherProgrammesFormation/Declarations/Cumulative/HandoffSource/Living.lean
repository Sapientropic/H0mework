import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.Joint
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffPayload.Formation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Install the actual recovered authoritative root and actual recovered
sealed handoff. The equality only aligns their already paid source indices. -/
def assembleLiving {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeLivingRootClosure N V)
    (restored : SourceNativeAuthoritativeRootClosure N V) (same : restored = old.toAuthoritativeRoot)
    (law : SourceNativeTerminalHandoffLaw old.source.base) : SourceNativeLivingRootClosure N V where
  source := ⟨restored.source, Equiv.cast (congrArg SourceNativeTerminalHandoffLaw
    (congrArg SourceNativeAuthoritativeRootClosure.source same).symm) law⟩
  emitted := restored.emitted
  compiler_commutes := restored.compiler_commutes

theorem assembleLiving_eq {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeLivingRootClosure N V)
    (restored : SourceNativeAuthoritativeRootClosure N V) (same : restored = old.toAuthoritativeRoot)
    (law : SourceNativeTerminalHandoffLaw old.source.base) (lawSame : law = old.source.terminalHandoff) :
    assembleLiving old restored same law = old := by
  cases old with
  | mk source emitted commutes =>
    cases source
    cases same
    cases lawSame
    rfl

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeLivingRootClosure N V) {events : EventFamily old.source.base}
    (declaration : Declaration old.source.base events)
    (jointMaterial : MotherArenaHigher.Material rank) (value : JointValue rank)
    (formed : formJoint jointMaterial = some value)
    (presentation : JointPresentation old.toAuthoritativeRoot events declaration value)

def payloadCoordinates := MotherHandoffPayload.coordinatesOfHandoffRoots declaration
  (MotherArenaHigher.split rank jointMaterial).1 value.1 (joint_root_formed jointMaterial value formed) presentation.authority
  (MotherArenaHigher.split rank jointMaterial).2 value.2 (joint_handoff_formed jointMaterial value formed) presentation.handoff

def formPayload (material : MotherArenaHigher.Material rank) :=
  MotherHandoffPayload.formValues (fun point => (declaration.continuation point).next)
    (payloadCoordinates old declaration jointMaterial value formed presentation) material

def readLaw (payload : MotherHandoffPayload.Values (fun point => (declaration.continuation point).next))
    (same : payload = MotherHandoffPayload.valuesOf declaration) : SourceNativeTerminalHandoffLaw old.source.base :=
  assembleLaw (MotherHandoffPayload.assembleRestored (fun point => (declaration.continuation point).next)
    presentation.handoff.restrictRoots presentation.handoff.restrictRoots_eq
    (MotherHandoffPayload.restrictEmit (root := old.toAuthoritativeRoot) declaration value.2 presentation.handoff) payload
    (MotherHandoffPayload.recovered_laws declaration payload same))

theorem readLaw_eq (payload : MotherHandoffPayload.Values (fun point => (declaration.continuation point).next))
    (same : payload = MotherHandoffPayload.valuesOf declaration) :
    readLaw old declaration value presentation payload same = assembleLaw declaration :=
  congrArg assembleLaw (MotherHandoffPayload.assembleRestored_recovers declaration
    presentation.handoff.restrictRoots presentation.handoff.restrictRoots_eq
    (MotherHandoffPayload.restrictEmit (root := old.toAuthoritativeRoot) declaration value.2 presentation.handoff)
    (MotherHandoffPayload.restrictEmit_eq (root := old.toAuthoritativeRoot) declaration value.2 presentation.handoff) payload same)

def restrictLiving (payload : MotherHandoffPayload.Values (fun point => (declaration.continuation point).next))
    (same : payload = MotherHandoffPayload.valuesOf declaration) : SourceNativeLivingRootClosure N V :=
  assembleLiving old presentation.authority.restrict presentation.authority.restrict_eq
    (readLaw old declaration value presentation payload same)

theorem restrictLiving_eq (payload : MotherHandoffPayload.Values (fun point => (declaration.continuation point).next))
    (same : payload = MotherHandoffPayload.valuesOf declaration)
    (lawSame : assembleLaw declaration = old.source.terminalHandoff) :
    restrictLiving old declaration value presentation payload same = old :=
  assembleLiving_eq old presentation.authority.restrict presentation.authority.restrict_eq _
    ((readLaw_eq old declaration value presentation payload same).trans lawSame)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
