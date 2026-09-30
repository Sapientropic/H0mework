import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.HandoffRoots.Factory
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityCoordinates.Restriction

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
open MotherHandoffEvents
noncomputable section
variable {rank : Ordinal.{0}}

def childMaterial (material : MotherArenaHigher.Material rank) (value : Value rank) (point : Point value.1.1) :=
  MotherArenaHigher.family rank (MotherArenaHigher.split rank material).2 (pointAddress value.1.1 point)

/-- The child is the actual parsed higher-material component, so its full
source and ledger coordinates follow from the existing formation decoder. -/
theorem child_formed (material : MotherArenaHigher.Material rank) (value : Value rank)
    (formed : formRoots material = some value) (point : Point value.1.1) :
    MotherArenaTheory.formTheory (childMaterial material value point) = some (value.2 point) := by
  unfold formRoots at formed
  dsimp only at formed
  obtain ⟨events, _eventsFormed, selected⟩ := Option.bind_eq_some_iff.mp formed
  unfold formParts at selected
  split at selected
  · rename_i checked
    have same := Option.some.inj selected
    cases same
    exact (Option.some_get (checked point)).symm
  · cases selected

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffRoots
