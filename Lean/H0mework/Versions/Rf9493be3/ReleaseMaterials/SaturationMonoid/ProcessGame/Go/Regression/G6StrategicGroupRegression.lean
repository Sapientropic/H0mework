import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.StrategicGroupLineage
import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Regression.G2GroupLineageRegression

/-!
# G6 virtual-connection and strategic-group regression

The G2 bridge current is consumed in two ways.  The original black bridge
strictly merges its two chains.  After a generated black pass, a two-ply
possible continuation still connects them, but the actual white occupation
of the connector point destroys that bounded possibility.  Both strict black
chains survive the actual block and remain distinct; only their old strategic
component splits.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G6StrategicGroupRegression

open G2GroupLineageRegression

def p21 : Point 3 := (2, 1)

/-! ## Exact source after Black passes -/

theorem source_pass_target_isSome :
    (nativeStep? zeroKomiLaw mergePrefixReplay.final (.pass : Move 3)).isSome =
      true := by
  decide

def sourcePassTarget : Frame 3 :=
  (nativeStep? zeroKomiLaw mergePrefixReplay.final (.pass : Move 3)).get
    source_pass_target_isSome

def sourcePassPly : GeneratedReplay.ActualPly mergePrefixReplay where
  target := sourcePassTarget
  emitted := .pass
  step := by
    unfold LegalStep
    exact (Option.some_get source_pass_target_isSome).symm

def strategicSourceReplay := sourcePassPly.extended

def sourceLeftStone : OccupiedStone strategicSourceReplay.final.visible.board where
  point := p00
  polarity := .positive
  occupied := by decide

def sourceRightStone : OccupiedStone strategicSourceReplay.final.visible.board where
  point := p02
  polarity := .positive
  occupied := by decide

def sourceLeftGroup : SnapshotGroup strategicSourceReplay.final.visible.board :=
  snapshotGroupOf sourceLeftStone

def sourceRightGroup : SnapshotGroup strategicSourceReplay.final.visible.board :=
  snapshotGroupOf sourceRightStone

/-! ## Exact two-ply possible connector -/

def connectorWord : List (Move 3) := [.play p21, .play p01]

theorem connector_white_target_isSome :
    (nativeStep? zeroKomiLaw strategicSourceReplay.final (.play p21)).isSome =
      true := by
  decide

def connectorWhiteTarget : Frame 3 :=
  (nativeStep? zeroKomiLaw strategicSourceReplay.final (.play p21)).get
    connector_white_target_isSome

theorem connectorWhiteStep :
    LegalStep zeroKomiLaw strategicSourceReplay.final (.play p21)
      connectorWhiteTarget := by
  unfold LegalStep
  exact (Option.some_get connector_white_target_isSome).symm

theorem connector_black_target_isSome :
    (nativeStep? zeroKomiLaw connectorWhiteTarget (.play p01)).isSome = true := by
  decide

def connectorBlackTarget : Frame 3 :=
  (nativeStep? zeroKomiLaw connectorWhiteTarget (.play p01)).get
    connector_black_target_isSome

theorem connectorBlackStep :
    LegalStep zeroKomiLaw connectorWhiteTarget (.play p01)
      connectorBlackTarget := by
  unfold LegalStep
  exact (Option.some_get connector_black_target_isSome).symm

def connectorContinuation :
    GeneratedReplay zeroKomiLaw strategicSourceReplay.final connectorWord :=
  .cons (.play p21) connectorWhiteStep
    (.cons (.play p01) connectorBlackStep (.nil connectorBlackTarget))

theorem connector_final_strict_group_common :
    groupAt connectorContinuation.final.visible.board p00 =
      groupAt connectorContinuation.final.visible.board p02 := by
  decide

def connectorExactCommonSuccessor :
    ExactCommonSuccessorAt zeroKomiLaw strategicSourceReplay.final 2
      sourceLeftGroup.carrier sourceRightGroup.carrier where
  word := connectorWord
  bounded := by decide
  continuation := connectorContinuation
  leftPoint := p00
  rightPoint := p02
  polarity := .positive
  left_source := by decide
  right_source := by decide
  left_mem := by decide
  right_mem := by decide
  left_survives := by decide
  right_survives := by decide
  common_target := connector_final_strict_group_common

theorem connector_word_is_generated_witness :
    connectorWord ∈ virtualConnectionWords zeroKomiLaw
      strategicSourceReplay.final 2 sourceLeftGroup.carrier
        sourceRightGroup.carrier := by
  decide

theorem source_virtual_connection :
    VirtualConnectionAt strategicSourceReplay 2
      sourceLeftGroup sourceRightGroup := by
  decide

theorem source_virtual_connection_has_exact_common_successor :
    Nonempty (ExactCommonSuccessorAt zeroKomiLaw
      strategicSourceReplay.final 2 sourceLeftGroup.carrier
        sourceRightGroup.carrier) :=
  source_virtual_connection.exactCommonSuccessor

theorem source_virtual_connection_is_same_cone_path :
    ∃ witness : ExactCommonSuccessorAt zeroKomiLaw
        strategicSourceReplay.final 2 sourceLeftGroup.carrier
          sourceRightGroup.carrier,
      witness.continuation.stateTrace ∈
        rootedPaths (futureConeAt strategicSourceReplay 2) :=
  source_virtual_connection.factors_through_futureCone

/-! ## Actual White block -/

theorem block_target_isSome :
    (nativeStep? zeroKomiLaw strategicSourceReplay.final (.play p01)).isSome =
      true := by
  decide

def blockTarget : Frame 3 :=
  (nativeStep? zeroKomiLaw strategicSourceReplay.final (.play p01)).get
    block_target_isSome

def blockPly : GeneratedReplay.ActualPly strategicSourceReplay where
  target := blockTarget
  emitted := .play p01
  step := by
    unfold LegalStep
    exact (Option.some_get block_target_isSome).symm

def blockedReplay := blockPly.extended

def blockedLeftStone : OccupiedStone blockTarget.visible.board where
  point := p00
  polarity := .positive
  occupied := by decide

def blockedRightStone : OccupiedStone blockTarget.visible.board where
  point := p02
  polarity := .positive
  occupied := by decide

def blockedLeftGroup : SnapshotGroup blockTarget.visible.board :=
  snapshotGroupOf blockedLeftStone

def blockedRightGroup : SnapshotGroup blockTarget.visible.board :=
  snapshotGroupOf blockedRightStone

def blockedLeftSurvivor : SurvivingStone
    strategicSourceReplay.final.visible.board blockTarget.visible.board where
  point := p00
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

def blockedRightSurvivor : SurvivingStone
    strategicSourceReplay.final.visible.board blockTarget.visible.board where
  point := p02
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

theorem blockedLeftTransport :
    StrategicGroupTransportAt blockPly 2 sourceLeftGroup blockedLeftGroup where
  strictTransport := ⟨blockedLeftSurvivor, rfl, rfl⟩

theorem blockedRightTransport :
    StrategicGroupTransportAt blockPly 2 sourceRightGroup blockedRightGroup where
  strictTransport := ⟨blockedRightSurvivor, rfl, rfl⟩

theorem blocked_strict_groups_distinct : blockedLeftGroup ≠ blockedRightGroup := by
  apply SnapshotGroup.eq_iff_carrier_eq.not.mpr
  decide

theorem source_strategic_clusters_equal :
    strategicGroupOf strategicSourceReplay 2 sourceLeftGroup =
      strategicGroupOf strategicSourceReplay 2 sourceRightGroup := by
  decide

theorem block_removes_virtual_connection :
    ¬ VirtualConnectionCarrierAt zeroKomiLaw blockTarget 2
      blockedLeftGroup.carrier blockedRightGroup.carrier := by
  decide

theorem blocked_strategic_clusters_distinct :
    strategicClusterFrom zeroKomiLaw blockTarget 2 blockedLeftGroup ≠
      strategicClusterFrom zeroKomiLaw blockTarget 2 blockedRightGroup := by
  decide

def strategicSplit : StrategicSplitDispositionAt blockPly 2 where
  sourceLeft := sourceLeftGroup
  sourceRight := sourceRightGroup
  targetLeft := blockedLeftGroup
  targetRight := blockedRightGroup
  sourceVirtual := source_virtual_connection
  sourceClusterEq := source_strategic_clusters_equal
  leftTransport := blockedLeftTransport
  rightTransport := blockedRightTransport
  strictTargetsDistinct := blocked_strict_groups_distinct
  targetNotVirtual := block_removes_virtual_connection
  targetClustersDistinct := blocked_strategic_clusters_distinct

/-! ## Original G2 bridge as strict and strategic merge -/

theorem original_bridge_virtual_connection :
    VirtualConnectionAt mergePrefixReplay 1
      bridgeMerge.left.sourceGroup bridgeMerge.right.sourceGroup := by
  decide

theorem original_bridge_source_strategic_clusters_equal :
    strategicGroupOf mergePrefixReplay 1 bridgeMerge.left.sourceGroup =
      strategicGroupOf mergePrefixReplay 1 bridgeMerge.right.sourceGroup := by
  decide

def strategicMerge : StrategicMergeDispositionAt bridgePly 1 where
  strictMerge := bridgeMerge
  sourceVirtual := original_bridge_virtual_connection
  sourceClusterEq := original_bridge_source_strategic_clusters_equal

/-! ## Direct consumers -/

theorem original_bridge_merges_strict_and_strategic :
    bridgeMerge.left.sourceGroup ≠ bridgeMerge.right.sourceGroup ∧
      strategicGroupOf mergePrefixReplay 1 bridgeMerge.left.sourceGroup =
        strategicGroupOf mergePrefixReplay 1 bridgeMerge.right.sourceGroup ∧
      bridgeMerge.left.targetGroup = bridgeMerge.right.targetGroup :=
  ⟨bridgeMerge.distinctSources,
    strategicMerge.sourceClusterEq,
    bridgeMerge.commonTarget⟩

theorem actual_block_preserves_two_distinct_strict_chains :
    ActualExactGroupTransport blockPly sourceLeftGroup blockedLeftGroup ∧
      ActualExactGroupTransport blockPly sourceRightGroup blockedRightGroup ∧
      blockedLeftGroup ≠ blockedRightGroup :=
  ⟨strategicSplit.leftTransport.strictTransport,
    strategicSplit.rightTransport.strictTransport,
    strategicSplit.strictTargetsDistinct⟩

theorem actual_block_splits_only_the_strategic_group :
    strategicGroupOf strategicSourceReplay 2 sourceLeftGroup =
        strategicGroupOf strategicSourceReplay 2 sourceRightGroup ∧
      strategicClusterFrom zeroKomiLaw blockTarget 2 blockedLeftGroup ≠
        strategicClusterFrom zeroKomiLaw blockTarget 2 blockedRightGroup ∧
      IsEmpty (ActualSplitDisposition blockPly) :=
  ⟨strategicSplit.sourceClusterEq,
    strategicSplit.targetClustersDistinct,
    actualPly_noPartialChainSplit blockPly⟩

end G6StrategicGroupRegression
end Go
end ProcessGame
end SaturationMonoid
