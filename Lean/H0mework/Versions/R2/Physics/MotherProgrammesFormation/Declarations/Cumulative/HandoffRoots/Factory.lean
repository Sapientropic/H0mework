import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffEvents.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Header

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
open MotherHandoffEvents
noncomputable section
open scoped Classical
variable {rank : Ordinal.{0}}

abbrev Value (rank : Ordinal.{0}) :=
  Σ events : MotherHandoffEvents.Value rank, Point events.1 → MotherAuthorityFamilies.Output

/-- Every event in the complete formed fibre has its own complete root
declaration. The emitter does not restrict this family. -/
def formParts (events : MotherHandoffEvents.Value rank) (programmes : MotherArenaHigher.Material rank) : Option (Value rank) :=
  if checked : ∀ point : Point events.1,
      (MotherArenaTheory.formTheory (MotherArenaHigher.family rank programmes (pointAddress events.1 point))).isSome then
    some ⟨events, fun point =>
      (MotherArenaTheory.formTheory (MotherArenaHigher.family rank programmes (pointAddress events.1 point))).get (checked point)⟩
  else none

def formRoots (material : MotherArenaHigher.Material rank) : Option (Value rank) :=
  let parts := MotherArenaHigher.split rank material
  (MotherHandoffEvents.formEvents parts.1).bind (fun events => formParts events parts.2)

theorem roots_on_events (parent : MotherArenaHigher.Material rank) (events : MotherHandoffEvents.Value rank)
    (parentFormed : MotherHandoffEvents.formEvents parent = some events)
    (children : Point events.1 → MotherAuthorityFamilies.Output)
    (materials : Point events.1 → MotherArenaHigher.Material rank)
    (formed : ∀ point, MotherArenaTheory.formTheory (materials point) = some (children point)) :
    ∃ material : MotherArenaHigher.Material rank, formRoots material = some ⟨events, children⟩ := by
  let address := pointAddress events.1
  let extension : MotherArenaHigher.Base rank → MotherArenaHigher.Material rank := fun code =>
    if present : ∃ point, address point = code then materials (Classical.choose present) else parent
  let programmes := (MotherArenaHigher.familyEquiv rank).symm extension
  have program_at (point : Point events.1) :
      MotherArenaHigher.family rank programmes (address point) = materials point := by
    change (MotherArenaHigher.familyEquiv rank) ((MotherArenaHigher.familyEquiv rank).symm extension) (address point) = _
    rw [Equiv.apply_symm_apply]
    have present : ∃ other, address other = address point := ⟨point, rfl⟩
    simp only [extension, dif_pos present]
    exact congrArg materials (address.injective (Classical.choose_spec present))
  have available : ∀ point : Point events.1,
      (MotherArenaTheory.formTheory (MotherArenaHigher.family rank programmes (address point))).isSome := by
    intro point
    rw [program_at, formed]
    rfl
  refine ⟨MotherArenaHigher.pack rank (parent, programmes), ?_⟩
  unfold formRoots
  rw [MotherArenaHigher.split_pack]
  dsimp only
  rw [parentFormed, Option.bind_some, formParts, dif_pos available]
  apply congrArg some
  apply congrArg (Sigma.mk events)
  funext point
  exact Option.some.inj ((Option.some_get (available point)).trans
    ((congrArg MotherArenaTheory.formTheory (program_at point)).trans (formed point)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
