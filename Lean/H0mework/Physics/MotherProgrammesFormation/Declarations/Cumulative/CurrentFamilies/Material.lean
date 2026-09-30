import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.NativeCurrent.AtRank
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCurrentFamilies
open MotherArenaNetwork
noncomputable section
open scoped Classical
variable {rank : Ordinal.{0}}

def domain (material : MotherArenaHigher.Material rank) := (MotherArenaHigher.split rank material).1
abbrev Member (material : MotherArenaHigher.Material rank) := MotherAuthorityFamilies.Member (domain material)

def components (material : MotherArenaHigher.Material rank) :=
  let parts := MotherArenaHigher.split rank material
  (parts.1, MotherArenaHigher.split rank parts.2)

def memberMaterial (material : MotherArenaHigher.Material rank) (index : Member material) :=
  MotherArenaHigher.family rank (MotherArenaHigher.split rank material).2 index.val

def atMember (material : MotherArenaHigher.Material rank) (index : Member material) :=
  components (memberMaterial material index)

def packComponents (values : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank) :=
  MotherArenaHigher.pack rank (values.1, MotherArenaHigher.pack rank values.2)

theorem components_pack (values : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank) :
    components (packComponents values) = values := by
  simp only [components, packComponents, MotherArenaHigher.split_pack]

private theorem cast_member_val {first last : MotherArenaHigher.Material rank} (same : first = last)
    (index : MotherAuthorityFamilies.Member first) :
    (Equiv.cast (congrArg MotherAuthorityFamilies.Member same) index).val = index.val := by
  cases same
  rfl

/-- Whole indexed materials, including dormant or repeated semantic values,
form through the full higher-law family. Membership is a separate material
graph and does not depend on the emitter's chosen trajectory. -/
theorem every_material_family (I : Type) (base : MotherArenaHigher.Material rank)
    (indexMap : I ≃ MotherAuthorityFamilies.Member base)
    (values : I → MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank) :
    ∃ material : MotherArenaHigher.Material rank, ∃ indices : I ≃ Member material,
      ∀ index, atMember material (indices index) = values index := by
  let extension : MotherArenaHigher.Base rank → MotherArenaHigher.Material rank := fun code =>
    if present : bit base 0 code then packComponents (values (indexMap.symm ⟨code, present⟩)) else base
  let programmes := (MotherArenaHigher.familyEquiv rank).symm extension
  let material := MotherArenaHigher.pack rank (base, programmes)
  have baseSame : domain material = base := by
    unfold domain material
    rw [MotherArenaHigher.split_pack]
  let indices : I ≃ Member material := indexMap.trans (Equiv.cast (congrArg MotherAuthorityFamilies.Member baseSame.symm))
  have index_val (index : I) : (indices index).val = (indexMap index).val :=
    cast_member_val baseSame.symm (indexMap index)
  refine ⟨material, indices, fun index => ?_⟩
  unfold atMember memberMaterial
  rw [index_val]
  have parts : MotherArenaHigher.split rank material = (base, programmes) := MotherArenaHigher.split_pack rank _
  rw [parts]
  change components ((MotherArenaHigher.familyEquiv rank) ((MotherArenaHigher.familyEquiv rank).symm extension) (indexMap index).val) = _
  rw [Equiv.apply_symm_apply]
  simp only [extension, dif_pos (indexMap index).property, components_pack]
  change values (indexMap.symm (indexMap index)) = values index
  rw [indexMap.symm_apply_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCurrentFamilies
