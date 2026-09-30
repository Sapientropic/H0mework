import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRoot.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityFamilies
open MotherInventoryAdmission MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}

abbrev Member (material : MotherArenaHigher.Material rank) :=
  { code : MotherArenaHigher.Base rank // bit material 0 code }

abbrev Output :=
  Σ declaration : (Σ value : SourcePair, PresentationData value), TheoryState declaration.1.1.1.1.1.1

abbrev FamilyValue (rank : Ordinal.{0}) :=
  Σ domain : MotherArenaHigher.Material rank, Member domain → Output

/-- Both the entire index carrier and every complete declaration are read
from mother material. No root, event, or target family is a factory input. -/
def formFamilyParts (domain programmes : MotherArenaHigher.Material rank) : Option (FamilyValue rank) :=
  if checked : ∀ index : Member domain,
      (MotherArenaTheory.formTheory (MotherArenaHigher.family rank programmes index.val)).isSome then
    some ⟨domain, fun index =>
      (MotherArenaTheory.formTheory (MotherArenaHigher.family rank programmes index.val)).get (checked index)⟩
  else none

def formFamily (material : MotherArenaHigher.Material rank) : Option (FamilyValue rank) :=
  let parts := MotherArenaHigher.split rank material
  formFamilyParts parts.1 parts.2

/-- A whole family of already formed child materials is itself formed by
the signed higher mother-law family operation, at the same rank. -/
theorem family_on_members (domain : MotherArenaHigher.Material rank)
    (children : Member domain → Output)
    (materials : Member domain → MotherArenaHigher.Material rank)
    (formed : ∀ index, MotherArenaTheory.formTheory (materials index) = some (children index)) :
    ∃ material : MotherArenaHigher.Material rank, formFamily material = some ⟨domain, children⟩ := by
  let extension : MotherArenaHigher.Base rank → MotherArenaHigher.Material rank := fun code =>
    if present : bit domain 0 code then materials ⟨code, present⟩ else domain
  let programmes := (MotherArenaHigher.familyEquiv rank).symm extension
  have program_at (index : Member domain) : MotherArenaHigher.family rank programmes index.val = materials index := by
    change (MotherArenaHigher.familyEquiv rank) ((MotherArenaHigher.familyEquiv rank).symm extension) index.val = _
    rw [Equiv.apply_symm_apply]
    simp only [extension, dif_pos index.property]
  have available : ∀ index : Member domain,
      (MotherArenaTheory.formTheory (MotherArenaHigher.family rank programmes index.val)).isSome := by
    intro index
    rw [program_at, formed]
    rfl
  refine ⟨MotherArenaHigher.pack rank (domain, programmes), ?_⟩
  unfold formFamily
  rw [MotherArenaHigher.split_pack]
  dsimp only
  rw [formFamilyParts, dif_pos available]
  apply congrArg some
  apply congrArg (Sigma.mk domain)
  funext index
  apply Option.some.inj
  exact (Option.some_get (available index)).trans ((congrArg MotherArenaTheory.formTheory (program_at index)).trans (formed index))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityFamilies
