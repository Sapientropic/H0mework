import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.AtRank

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
open MotherHandoffRestriction MotherHandoffSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

structure Restriction (rank : Ordinal.{0}) {N : WorldRelationNetwork.{0}}
    (old : SourceNativeLivingRootCurrentAt N) (materials :
      MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank) where
  value : JointValue rank
  formed : formJoint materials.1 = some value
  events : EventFamily old.root.source.base
  declaration : Declaration old.root.source.base events
  presentation : JointPresentation old.root.toAuthoritativeRoot events declaration value
  available : (formPayload old.root declaration materials.1 value formed presentation materials.2.1).isSome
  same : (formPayload old.root declaration materials.1 value formed presentation materials.2.1).get available =
    MotherHandoffPayload.valuesOf declaration
  current_formed : formCurrent (restrictHeader old.root declaration value presentation
    ((formPayload old.root declaration materials.1 value formed presentation materials.2.1).get available) same)
    materials.2.2 = some old

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}} {old : SourceNativeLivingRootCurrentAt N}
    {materials : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank}

theorem CurrentFormationAt.restriction (formed : CurrentFormationAt rank old materials) :
    Nonempty (Restriction rank old materials) := by
  rcases formed with ⟨value, formed, events, declaration, presentation, available, same, currentFormed⟩
  exact ⟨⟨value, formed, events, declaration, presentation, available, same, currentFormed⟩⟩

/-- The actual final Option value is consumed. The original current occurs
only as the inverse type schema and the right side of the recovery theorem. -/
def Restriction.read (p : Restriction rank old materials) : SourceNativeLivingRootCurrentAt N :=
  let header := restrictHeader old.root p.declaration p.value p.presentation
    ((formPayload old.root p.declaration materials.1 p.value p.formed p.presentation materials.2.1).get p.available) p.same
  (formCurrent header materials.2.2).get (by rw [p.current_formed]; rfl)

theorem Restriction.read_eq (p : Restriction rank old materials) : p.read = old :=
  Option.some.inj ((Option.some_get _).trans p.current_formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeCurrent
