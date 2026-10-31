import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Society.GeneratedGroupRelationRole
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Future.RelationIndexedFuture

/-!
# Exact Go bridge for compiler-owned relation futures

The Go relation compilers own their bounded move carrier and dependent
continuation fibres.  These theorems identify the resulting generic future
codes with the existing G3/G4 `FutureFreedomCodesAt`; no future face or finset
is accepted from a consumer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace Society
namespace RelationFutureAuthority

open ProcessGame.Society Relations

def toGoSide : EdgeSide → Future.RelationEdgeSide :=
  GeneratedRelationRole.toFutureSide

theorem player_codesAt_eq_exactFutureFreedom
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix)
    (seed : GeneratedRelationRole.RelationSeed ply) (side : EdgeSide) :
    (GeneratedRelationRole.compiler horizon ply).futureCodesAt
        (GeneratedRelationRole.generatedRelationOf horizon ply seed) side =
      Future.FutureFreedomCodesAt
        (GeneratedRelationRole.phaseEdge horizon ply seed) (toGoSide side) := by
  classical
  ext word
  rw [SourceOwnedRelationRoleCompiler.mem_futureCodesAt_iff,
    Future.mem_FutureFreedomCodesAt_iff]
  constructor
  · exact fun facts => facts.2
  · rintro ⟨habitable⟩
    refine ⟨?_, ⟨habitable⟩⟩
    simpa using
      (mem_moveWordsUpTo_iff_length_le word horizon).mpr habitable.bounded

theorem player_actionableCodesAt_eq_exactActionableFreedom
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix)
    (seed : GeneratedRelationRole.RelationSeed ply) (side : EdgeSide) :
    (GeneratedRelationRole.compiler horizon ply).actionableFutureCodesAt
        (GeneratedRelationRole.generatedRelationOf horizon ply seed) side =
      Future.ActionableFutureFreedomCodesAt
        (GeneratedRelationRole.phaseEdge horizon ply seed) (toGoSide side) := by
  classical
  ext word
  rw [SourceOwnedRelationRoleCompiler.mem_actionableFutureCodesAt_iff,
    Future.mem_ActionableFutureFreedomCodesAt_iff]
  constructor
  · rintro ⟨_carrier, inhabited, nonidle⟩
    exact ⟨inhabited, nonidle⟩
  · rintro ⟨⟨habitable⟩, nonidle⟩
    refine ⟨?_, ⟨habitable⟩, nonidle⟩
    simpa using
      (mem_moveWordsUpTo_iff_length_le word horizon).mpr habitable.bounded

theorem group_codesAt_eq_exactFutureFreedom
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replayPrefix : GeneratedReplay law (Frame.initial n) moves}
    (horizon : Nat) (ply : GeneratedReplay.ActualPly replayPrefix)
    (stone : GeneratedGroupRelationRole.RelationSeed ply) (side : EdgeSide) :
    (GeneratedGroupRelationRole.compiler horizon ply).futureCodesAt
        (GeneratedGroupRelationRole.generatedRelationOf horizon ply stone)
        side =
      Future.FutureFreedomCodesAt
        (GeneratedGroupRelationRole.phaseEdge horizon ply stone)
        (toGoSide side) := by
  classical
  ext word
  rw [SourceOwnedRelationRoleCompiler.mem_futureCodesAt_iff,
    Future.mem_FutureFreedomCodesAt_iff]
  constructor
  · exact fun facts => facts.2
  · rintro ⟨habitable⟩
    refine ⟨?_, ⟨habitable⟩⟩
    simpa using
      (mem_moveWordsUpTo_iff_length_le word horizon).mpr habitable.bounded

end RelationFutureAuthority
end Society
end Go
end ProcessGame
end SaturationMonoid
