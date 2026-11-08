import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.GeneratedDancers
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2GroupLineageRegression

/-!
# G2 combined generated-dancers regression

The reachable 3×3 bridge replay consumes player and group generation in one
module.  This is the integration gate that prevents either lineage subsystem
from issuing a sibling replay continuation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G2GeneratedDancersRegression

open G2GroupLineageRegression

def bridgeDancers : GeneratedDancersAt bridgePly.extended :=
  generatedDancersAt bridgePly.extended

def bridgeMoveIndex : Fin (mergePrefixMoves ++ [Move.play p01]).length :=
  ⟨4, by decide⟩

/-- The bridge event has one exact generated owner in the same replay that
generates the merging snapshot groups. -/
theorem bridge_move_owner_unique :
    ∃! generated : GeneratedReplay.GeneratedPlayer bridgePly.extended,
      bridgePly.extended.EventOwnedBy bridgeMoveIndex generated :=
  bridgePly.extended.everyMoveOwnedByExactlyOneGeneratedPlayer bridgeMoveIndex

/-- The final bridge stone generates its timed snapshot group and persistent
transport-lineage identity through the joint G2 mouth. -/
theorem merged_stone_snapshot_exact :
    StoneBelongsToSnapshotGroup timedMergedStone
      (bridgeDancers.snapshotGroup afterBridgeTime timedMergedStone) :=
  bridgeDancers.snapshot_exact afterBridgeTime timedMergedStone

theorem merged_group_identity_is_replay_generated :
    bridgeDancers.groupIdentity afterBridgeTime timedMergedStone =
      generatedGroupIdentityOf timedMergedGroup := by
  rfl

/-- The two old source groups share that persistent identity only through the
two exact adjacent transport edges. -/
theorem bridge_sources_share_generated_identity :
    generatedGroupIdentityOf timedLeftGroup =
      generatedGroupIdentityOf timedRightGroup :=
  merge_generates_shared_replay_identity

end G2GeneratedDancersRegression
end Go
end ProcessGame
end SaturationMonoid
