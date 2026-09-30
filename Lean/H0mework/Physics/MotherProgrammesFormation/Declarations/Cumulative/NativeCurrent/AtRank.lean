import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.Consumer
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffSource.AtRank

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
open MotherHandoffRestriction MotherHandoffSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- Actual per-node readback for a complete current registry. Original types
are inverse schemas; all fields and the exact visit come from the three
material components. -/
abbrev CurrentFormationAt (rank : Ordinal.{0}) {N : WorldRelationNetwork.{0}}
    (old : SourceNativeLivingRootCurrentAt N) (materials :
      MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank) : Prop :=
  ∃ value : JointValue rank, ∃ formed : formJoint materials.1 = some value,
    ∃ events : EventFamily old.root.source.base, ∃ declaration : Declaration old.root.source.base events,
    ∃ presentation : JointPresentation old.root.toAuthoritativeRoot events declaration value,
    ∃ available : (formPayload old.root declaration materials.1 value formed presentation materials.2.1).isSome,
      let payload := (formPayload old.root declaration materials.1 value formed presentation materials.2.1).get available
      ∃ same : payload = MotherHandoffPayload.valuesOf declaration,
        formCurrent (restrictHeader old.root declaration value presentation payload same) materials.2.2 = some old

theorem current_at_rank {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
    (old : SourceNativeLivingRootCurrentAt N)
    (events : EventFamily old.root.source.base) (declaration : Declaration old.root.source.base events)
    (lawSame : assembleLaw declaration = old.root.source.terminalHandoff)
    (address : JointAddress old.root.toAuthoritativeRoot events declaration ↪ MotherArenaHigher.Base rank) :
    ∃ materials, CurrentFormationAt rank old materials := by
  obtain ⟨jointMaterial, payloadMaterial, value, formed, events, declaration, presentation,
    payload, payloadFormed, same, rootSame⟩ := living_at_rank N old.V old.root events declaration lawSame address
  obtain ⟨visitMaterial, currentFormed⟩ := current_on_header (rank := rank) old
    (restrictHeader old.root declaration value presentation payload same)
    (restrictHeader_of_root_eq old.root declaration value presentation payload same rootSame)
  have available : (formPayload old.root declaration jointMaterial value formed presentation payloadMaterial).isSome := by
    rw [payloadFormed]
    rfl
  have payloadEq : (formPayload old.root declaration jointMaterial value formed presentation payloadMaterial).get available = payload :=
    Option.some.inj ((Option.some_get available).trans payloadFormed)
  cases payloadEq
  exact ⟨(jointMaterial, payloadMaterial, visitMaterial), value, formed, events, declaration,
    presentation, available, same, currentFormed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
