import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.VirtualConnection

/-!
# Strategic-group lineage across actual Go plies

Strategic groups are finite virtual-connection clusters, while strict chains
retain the G2 stone-transport identity.  These dependent dispositions record
actual strategic merge and split without turning either cluster into a
registry or pretending that a strict connected chain can partially split.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

/-- One strict chain survives an exact actual ply and thereby anchors a
strategic-group continuation. -/
structure StrategicGroupTransportAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat)
    (source : SnapshotGroup replay.final.visible.board)
    (target : SnapshotGroup ply.target.visible.board) : Prop where
  strictTransport : ActualExactGroupTransport ply source target

/-- Two source strict chains occupy one virtual component and an actual ply
merges them into one strict target chain. -/
structure StrategicMergeDispositionAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat) where
  strictMerge : ActualMergeDisposition ply
  sourceVirtual : VirtualConnectionAt replay horizon
    strictMerge.left.sourceGroup strictMerge.right.sourceGroup
  sourceClusterEq :
    strategicGroupOf replay horizon strictMerge.left.sourceGroup =
      strategicGroupOf replay horizon strictMerge.right.sourceGroup

/-- One old virtual component has two exact surviving strict-chain
descendants, but the target virtual graph places them in distinct canonical
strategic components. -/
structure StrategicSplitDispositionAt {n : Nat} {law : Law}
    {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) (horizon : Nat) where
  sourceLeft : SnapshotGroup replay.final.visible.board
  sourceRight : SnapshotGroup replay.final.visible.board
  targetLeft : SnapshotGroup ply.target.visible.board
  targetRight : SnapshotGroup ply.target.visible.board
  sourceVirtual : VirtualConnectionAt replay horizon sourceLeft sourceRight
  sourceClusterEq :
    strategicGroupOf replay horizon sourceLeft =
      strategicGroupOf replay horizon sourceRight
  leftTransport : StrategicGroupTransportAt ply horizon sourceLeft targetLeft
  rightTransport : StrategicGroupTransportAt ply horizon sourceRight targetRight
  strictTargetsDistinct : targetLeft ≠ targetRight
  targetNotVirtual :
    ¬ VirtualConnectionCarrierAt law ply.target horizon
      targetLeft.carrier targetRight.carrier
  targetClustersDistinct :
    strategicClusterFrom law ply.target horizon targetLeft ≠
      strategicClusterFrom law ply.target horizon targetRight

/-- A strategic split preserves each strict-chain carrier through exact G2
transport; only the higher virtual component branches. -/
theorem StrategicSplitDispositionAt.strict_chains_survive {n : Nat}
    {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {ply : GeneratedReplay.ActualPly replay} {horizon : Nat}
    (split : StrategicSplitDispositionAt ply horizon) :
    ActualExactGroupTransport ply split.sourceLeft split.targetLeft ∧
      ActualExactGroupTransport ply split.sourceRight split.targetRight :=
  ⟨split.leftTransport.strictTransport,
    split.rightTransport.strictTransport⟩

/-- The split mouth cannot be confused with G2 partial-chain split: its two
target strict chains remain distinct while each is an exact survivor. -/
theorem StrategicSplitDispositionAt.is_strategic_not_strict {n : Nat}
    {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {ply : GeneratedReplay.ActualPly replay} {horizon : Nat}
    (split : StrategicSplitDispositionAt ply horizon) :
    split.targetLeft ≠ split.targetRight ∧
      strategicClusterFrom law ply.target horizon split.targetLeft ≠
        strategicClusterFrom law ply.target horizon split.targetRight :=
  ⟨split.strictTargetsDistinct, split.targetClustersDistinct⟩

end Go
end ProcessGame
end SaturationMonoid
