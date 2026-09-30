import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
open MotherHandoffRestriction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Complete component readback at one supplied sufficient rank. The two
material components are packed together by the source and family consumers. -/
abbrev LivingFormationAt (rank : Ordinal.{0}) {N : WorldRelationNetwork.{0}}
    {V : ConstructiveRoot.Vocabulary.{0}} (old : SourceNativeLivingRootClosure N V) : Prop :=
  ∃ jointMaterial payloadMaterial : MotherArenaHigher.Material rank,
    ∃ value : JointValue rank, ∃ formed : formJoint jointMaterial = some value,
    ∃ events : EventFamily old.source.base, ∃ declaration : Declaration old.source.base events,
    ∃ presentation : JointPresentation old.toAuthoritativeRoot events declaration value,
    ∃ payload : MotherHandoffPayload.Values (fun point => (declaration.continuation point).next),
      formPayload old declaration jointMaterial value formed presentation payloadMaterial = some payload ∧
      ∃ same : payload = MotherHandoffPayload.valuesOf declaration,
        restrictLiving old declaration value presentation payload same = old

theorem living_at_rank {rank : Ordinal.{0}} (N : WorldRelationNetwork.{0})
    (V : ConstructiveRoot.Vocabulary.{0}) (old : SourceNativeLivingRootClosure N V)
    (events : EventFamily old.source.base) (declaration : Declaration old.source.base events)
    (lawSame : assembleLaw declaration = old.source.terminalHandoff)
    (address : JointAddress old.toAuthoritativeRoot events declaration ↪ MotherArenaHigher.Base rank) :
    LivingFormationAt rank old := by
  obtain ⟨jointMaterial, value, formed, ⟨presentation⟩⟩ :=
    joint_at_rank old.toAuthoritativeRoot events declaration address
  obtain ⟨payloadMaterial, payloadFormed⟩ := MotherHandoffPayload.every_values
    (fun point => (declaration.continuation point).next)
    (payloadCoordinates old declaration jointMaterial value formed presentation)
    (MotherHandoffPayload.valuesOf declaration)
  exact ⟨jointMaterial, payloadMaterial, value, formed, events, declaration, presentation,
    MotherHandoffPayload.valuesOf declaration, payloadFormed, rfl,
    restrictLiving_eq old declaration value presentation _ rfl lawSame⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffSource
