import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Joint

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
noncomputable section

structure LowerParts (rank : Ordinal.{0}) where
  roots : MotherArenaHigher.Material rank
  header : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank
  queries : MotherArenaHigher.Material rank
  inputs : MotherArenaHigher.Material rank

def packLower {rank : Ordinal.{0}} (parts : LowerParts rank) : MotherArenaHigher.Material rank :=
  MotherArenaHigher.pack rank (parts.roots, MotherArenaHigher.pack rank
    (parts.header.1, MotherArenaHigher.pack rank (parts.header.2.1,
      MotherArenaHigher.pack rank (parts.header.2.2, MotherArenaHigher.pack rank (parts.queries, parts.inputs)))))

def unpackLower {rank : Ordinal.{0}} (material : MotherArenaHigher.Material rank) : LowerParts rank :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  let third := MotherArenaHigher.split rank second.2
  let fourth := MotherArenaHigher.split rank third.2
  let fifth := MotherArenaHigher.split rank fourth.2
  ⟨first.1, (second.1, third.1, fourth.1), fifth.1, fifth.2⟩

theorem unpack_packLower {rank : Ordinal.{0}} (parts : LowerParts rank) : unpackLower (packLower parts) = parts := by
  simp only [unpackLower, packLower, MotherArenaHigher.split_pack]

def readLower {lower : Ordinal.{0}} {upper : Ordinal.{3}}
    (address : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper)
    (material : MotherReceiptHigher.Material upper) : MotherArenaHigher.Material lower :=
  MotherReceiptHigher.restrictArena lower upper address (MotherReceiptHigher.split upper material).1

def readChild {upper : Ordinal.{3}} (material : MotherReceiptHigher.Material upper)
    (code : MotherReceiptHigher.Base upper) : MotherReceiptHigher.Material upper :=
  MotherReceiptHigher.family upper (MotherReceiptHigher.split upper material).2 code

/-- Only complete already formed materials are assembled here. The fixed
readers recover the complete lower bundle and every child material. -/
theorem every_material_bundle {lower : Ordinal.{0}} {upper : Ordinal.{3}} {I : Type}
    (address : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper)
    (lowerMaterial : MotherArenaHigher.Material lower)
    (index : I ↪ MotherReceiptHigher.Base upper) (values : I → MotherReceiptHigher.Material upper) :
    ∃ material : MotherReceiptHigher.Material upper,
      readLower address material = lowerMaterial ∧ ∀ i, readChild material (index i) = values i := by
  let retained := MotherReceiptHigher.includeArena lower upper address lowerMaterial
  let extension := Function.extend index values (fun _ => retained)
  let family := (MotherReceiptHigher.familyEquiv upper).symm extension
  let material := MotherReceiptHigher.pack upper (retained, family)
  refine ⟨material, ?_, fun i => ?_⟩
  · simp only [readLower, material, MotherReceiptHigher.split_pack, retained, MotherReceiptHigher.restrict_includeArena]
  · unfold readChild material
    rw [MotherReceiptHigher.split_pack]
    change (MotherReceiptHigher.familyEquiv upper) ((MotherReceiptHigher.familyEquiv upper).symm extension) (index i) = _
    rw [Equiv.apply_symm_apply]
    exact index.injective.extend_apply _ _ i

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
