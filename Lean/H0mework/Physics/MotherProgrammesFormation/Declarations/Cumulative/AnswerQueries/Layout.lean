import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.CurrentFamilies.Material

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
noncomputable section

structure Materials (rank : Ordinal.{0}) where
  current : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank
  header : MotherArenaHigher.Material rank × MotherArenaHigher.Material rank × MotherArenaHigher.Material rank
  queries : MotherArenaHigher.Material rank
  indices : MotherArenaHigher.Material rank
  clauses : MotherArenaHigher.Material rank

def pack {rank : Ordinal.{0}} (parts : Materials rank) : MotherArenaHigher.Material rank :=
  MotherArenaHigher.pack rank (MotherCurrentFamilies.packComponents parts.current,
    MotherArenaHigher.pack rank (MotherCurrentFamilies.packComponents parts.header,
      MotherArenaHigher.pack rank (parts.queries, MotherArenaHigher.pack rank (parts.indices, parts.clauses))))

def unpack {rank : Ordinal.{0}} (material : MotherArenaHigher.Material rank) : Materials rank :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  let third := MotherArenaHigher.split rank second.2
  let fourth := MotherArenaHigher.split rank third.2
  ⟨MotherCurrentFamilies.components first.1, MotherCurrentFamilies.components second.1, third.1, fourth.1, fourth.2⟩

theorem unpack_pack {rank : Ordinal.{0}} (parts : Materials rank) : unpack (pack parts) = parts := by
  simp only [unpack, pack, MotherArenaHigher.split_pack, MotherCurrentFamilies.components_pack]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
