import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Higher

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
noncomputable section

structure Child (rank : Ordinal.{0}) where
  face : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank
  body : MotherArenaHigher.Material rank

def packChild {rank : Ordinal.{0}} (child : Child rank) : MotherArenaHigher.Material rank :=
  MotherArenaHigher.pack rank (child.face.1, MotherArenaHigher.pack rank
    (child.face.2.1, MotherArenaHigher.pack rank (child.face.2.2, child.body)))

def unpackChild {rank : Ordinal.{0}} (material : MotherArenaHigher.Material rank) : Child rank :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  let third := MotherArenaHigher.split rank second.2
  ⟨(first.1, second.1, third.1), third.2⟩

theorem unpack_packChild {rank : Ordinal.{0}} (child : Child rank) : unpackChild (packChild child) = child := by
  simp only [unpackChild, packChild, MotherArenaHigher.split_pack]

structure Parts (rank : Ordinal.{0}) where
  roots : MotherArenaHigher.Material rank
  header : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank
  indices : MotherArenaHigher.Material rank
  inputs : MotherArenaHigher.Material rank
  children : MotherArenaHigher.Material rank

def packParts {rank : Ordinal.{0}} (parts : Parts rank) : MotherArenaHigher.Material rank :=
  MotherArenaHigher.pack rank (parts.roots, MotherArenaHigher.pack rank
    (parts.header.1, MotherArenaHigher.pack rank (parts.header.2.1, MotherArenaHigher.pack rank
      (parts.header.2.2, MotherArenaHigher.pack rank (parts.indices, MotherArenaHigher.pack rank (parts.inputs, parts.children))))))

def unpackParts {rank : Ordinal.{0}} (material : MotherArenaHigher.Material rank) : Parts rank :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  let third := MotherArenaHigher.split rank second.2
  let fourth := MotherArenaHigher.split rank third.2
  let fifth := MotherArenaHigher.split rank fourth.2
  let sixth := MotherArenaHigher.split rank fifth.2
  ⟨first.1, (second.1, third.1, fourth.1), fifth.1, sixth.1, sixth.2⟩

theorem unpack_packParts {rank : Ordinal.{0}} (parts : Parts rank) : unpackParts (packParts parts) = parts := by
  simp only [unpackParts, packParts, MotherArenaHigher.split_pack]

def childAt {rank : Ordinal.{0}} (material : MotherArenaHigher.Material rank)
    (code : MotherArenaHigher.Base rank) : Child rank :=
  unpackChild (MotherArenaHigher.family rank material code)

theorem every_children {rank : Ordinal.{0}} {I : Type}
    (index : I ↪ MotherArenaHigher.Base rank) (values : I → Child rank)
    (fallback : MotherArenaHigher.Material rank) :
    ∃ material : MotherArenaHigher.Material rank, ∀ i, childAt material (index i) = values i := by
  let extension := Function.extend index (fun i => packChild (values i)) (fun _ => fallback)
  let material := (MotherArenaHigher.familyEquiv rank).symm extension
  refine ⟨material, fun i => ?_⟩
  unfold childAt material
  change unpackChild ((MotherArenaHigher.familyEquiv rank) ((MotherArenaHigher.familyEquiv rank).symm extension) (index i)) = _
  rw [Equiv.apply_symm_apply]
  dsimp only [extension]
  rw [index.injective.extend_apply, unpack_packChild]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
