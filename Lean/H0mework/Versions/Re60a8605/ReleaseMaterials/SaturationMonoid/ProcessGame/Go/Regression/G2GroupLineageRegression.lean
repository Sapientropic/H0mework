import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.GeneratedGroupLineage
import Mathlib.Tactic.FinCases

/-!
# G2 generated group-lineage regression

The 3×3 bridge example supplies two exact old components and one common
successor.  The 2×2 capture example supplies a whole-carrier terminal
disposition.  A deliberately deleted bridge exhibits the generic split
transporter, while an exhaustive compiler check proves that this partial split
is not an actual successor of the reachable Go current.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G2GroupLineageRegression

def zeroKomiLaw : Law := Law.positionalSuperko 0

def p00 : Point 3 := (0, 0)
def p01 : Point 3 := (0, 1)
def p02 : Point 3 := (0, 2)
def p20 : Point 3 := (2, 0)
def p22 : Point 3 := (2, 2)

/-- Before the bridge move, the two positive corner stones are distinct
singleton groups.  Every frame is generated from `Frame.initial`. -/
def mergePrefixMoves : List (Move 3) :=
  [.play p00, .play p20, .play p02, .play p22]

theorem mergePrefix_generated_isSome :
    (generate? zeroKomiLaw 3 mergePrefixMoves).isSome = true := by
  decide

def mergePrefixReplay :
    GeneratedReplay zeroKomiLaw (Frame.initial 3) mergePrefixMoves :=
  (generate? zeroKomiLaw 3 mergePrefixMoves).get
    mergePrefix_generated_isSome

theorem bridge_generated_isSome :
    (nativeStep? zeroKomiLaw mergePrefixReplay.final (.play p01)).isSome = true := by
  decide

def bridgeTarget : Frame 3 :=
  (nativeStep? zeroKomiLaw mergePrefixReplay.final (.play p01)).get
    bridge_generated_isSome

theorem bridgeStep :
    LegalStep zeroKomiLaw mergePrefixReplay.final (.play p01) bridgeTarget := by
  unfold LegalStep
  decide

def bridgePly : GeneratedReplay.ActualPly mergePrefixReplay where
  target := bridgeTarget
  emitted := .play p01
  step := bridgeStep

def mergeReplayMoves : List (Move 3) :=
  mergePrefixMoves ++ [.play p01]

theorem mergeReplay_generated_isSome :
    (generate? zeroKomiLaw 3 mergeReplayMoves).isSome = true := by
  decide

def mergeReplay :
    GeneratedReplay zeroKomiLaw (Frame.initial 3) mergeReplayMoves :=
  (generate? zeroKomiLaw 3 mergeReplayMoves).get
    mergeReplay_generated_isSome

/-- The direct step target is the final current of the same generated replay,
so the group transition is not attached after the fact. -/
theorem mergeReplay_final_eq_bridgeTarget :
    mergeReplay.final = bridgeTarget := by
  decide

theorem mergeReplay_eq_actualPly_extended :
    mergeReplay = bridgePly.extended := by
  rfl

def bridgeLeft : SurvivingStone
    mergePrefixReplay.final.visible.board bridgeTarget.visible.board where
  point := p00
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

def bridgeRight : SurvivingStone
    mergePrefixReplay.final.visible.board bridgeTarget.visible.board where
  point := p02
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

/-- The actual bridge move merges two exact source components into one target
component. -/
def bridgeMerge : ActualMergeDisposition bridgePly where
  left := bridgeLeft
  right := bridgeRight
  distinctSources := by
    intro equalGroups
    have equalCarriers := SnapshotGroup.eq_iff_carrier_eq.mp equalGroups
    change groupAt mergePrefixReplay.final.visible.board p00 =
      groupAt mergePrefixReplay.final.visible.board p02 at equalCarriers
    have distinctCarriers :
        groupAt mergePrefixReplay.final.visible.board p00 ≠
          groupAt mergePrefixReplay.final.visible.board p02 := by
      decide
    exact distinctCarriers equalCarriers
  commonTarget := by
    apply SnapshotGroup.eq_iff_carrier_eq.mpr
    decide

/-- The merge mouth exposes one common successor and exact transports from
both old groups. -/
theorem bridge_left_exact_transport :
    ActualExactGroupTransport bridgePly bridgeMerge.left.sourceGroup
      bridgeMerge.successor :=
  bridgeMerge.left_transports_to_successor

theorem bridge_right_exact_transport :
    ActualExactGroupTransport bridgePly bridgeMerge.right.sourceGroup
      bridgeMerge.successor :=
  bridgeMerge.right_transports_to_successor

/-- Both singleton presentations have the same finite shape and polarity,
but they are not the same generated group before the bridge. -/
theorem lookalike_singletons_are_wrong_lineage :
    bridgeLeft.sourceGroup.carrier.card =
        bridgeRight.sourceGroup.carrier.card ∧
      bridgeLeft.sourceGroup ≠ bridgeRight.sourceGroup := by
  constructor
  · decide
  · exact bridgeMerge.distinctSources

/-- Kernel computation certifies source functionality on this exact actual
bridge transition; hence the legal step cannot partially split an old group. -/
theorem bridge_carrier_successor_coherent :
    CarrierSuccessorCoherent mergePrefixReplay.final.visible.board
      bridgeTarget.visible.board := by
  decide

theorem bridge_actual_split_isEmpty :
    IsEmpty (ActualSplitDisposition bridgePly) :=
  actualSplitDisposition_isEmpty_of_sourceSuccessorCoherent bridgePly
    (sourceSuccessorCoherent_of_carrier bridge_carrier_successor_coherent)

theorem bridge_merge_has_only_common_successor
    (stone : SurvivingStone mergePrefixReplay.final.visible.board
      bridgeTarget.visible.board)
    (fromParent : stone.sourceGroup = bridgeMerge.left.sourceGroup ∨
      stone.sourceGroup = bridgeMerge.right.sourceGroup) :
    stone.targetGroup = bridgeMerge.successor :=
  bridgeMerge.successor_unique_of_parent
    (sourceSuccessorCoherent_of_carrier bridge_carrier_successor_coherent)
    stone fromParent

/-! ## Replay-wide identity generated by exact adjacent transports -/

def beforeBridgeTime : Fin bridgePly.extended.toOccurrence.trace.length :=
  ⟨4, by decide⟩

def afterBridgeTime : Fin bridgePly.extended.toOccurrence.trace.length :=
  ⟨5, by decide⟩

def timedLeftStone : OccupiedStone
    ((bridgePly.extended.toOccurrence.trace.get beforeBridgeTime).visible.board) where
  point := p00
  polarity := .positive
  occupied := by decide

def timedRightStone : OccupiedStone
    ((bridgePly.extended.toOccurrence.trace.get beforeBridgeTime).visible.board) where
  point := p02
  polarity := .positive
  occupied := by decide

def timedMergedStone : OccupiedStone
    ((bridgePly.extended.toOccurrence.trace.get afterBridgeTime).visible.board) where
  point := p00
  polarity := .positive
  occupied := by decide

def timedLeftGroup : ReplaySnapshotGroup bridgePly.extended where
  time := beforeBridgeTime
  group := snapshotGroupOf timedLeftStone

def timedRightGroup : ReplaySnapshotGroup bridgePly.extended where
  time := beforeBridgeTime
  group := snapshotGroupOf timedRightStone

def timedMergedGroup : ReplaySnapshotGroup bridgePly.extended where
  time := afterBridgeTime
  group := snapshotGroupOf timedMergedStone

def timedLeftSurvivor : SurvivingStone
    ((bridgePly.extended.toOccurrence.trace.get beforeBridgeTime).visible.board)
    ((bridgePly.extended.toOccurrence.trace.get afterBridgeTime).visible.board) where
  point := p00
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

def timedRightSurvivor : SurvivingStone
    ((bridgePly.extended.toOccurrence.trace.get beforeBridgeTime).visible.board)
    ((bridgePly.extended.toOccurrence.trace.get afterBridgeTime).visible.board) where
  point := p02
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

theorem timedLeftEdge :
    ReplayGroupTransportEdge timedLeftGroup timedMergedGroup where
  consecutive := by decide
  transport := ⟨timedLeftSurvivor, rfl, rfl⟩

theorem timedRightEdge :
    ReplayGroupTransportEdge timedRightGroup timedMergedGroup where
  consecutive := by decide
  transport := by
    refine ⟨timedRightSurvivor, rfl, ?_⟩
    apply SnapshotGroup.eq_iff_carrier_eq.mpr
    decide

/-- Two different pre-merge snapshot classes acquire one persistent identity
only through the pair of exact adjacent edges in the generated replay. -/
theorem merge_generates_shared_replay_identity :
    generatedGroupIdentityOf timedLeftGroup =
      generatedGroupIdentityOf timedRightGroup := by
  apply generatedGroupIdentity_eq_iff_exactReplayLineage.mpr
  exact ExactReplayGroupLineage.trans timedLeftEdge.exactLineage
    (ExactReplayGroupLineage.symm timedRightEdge.exactLineage)

/-! ## Persistent lookalike rejection -/

def oppositeSingletonMoves : List (Move 3) :=
  [.play p00, .play p22]

theorem oppositeSingletonReplay_generated_isSome :
    (generate? zeroKomiLaw 3 oppositeSingletonMoves).isSome = true := by
  decide

def oppositeSingletonReplay :
    GeneratedReplay zeroKomiLaw (Frame.initial 3) oppositeSingletonMoves :=
  (generate? zeroKomiLaw 3 oppositeSingletonMoves).get
    oppositeSingletonReplay_generated_isSome

def oppositeSingletonTime :
    Fin oppositeSingletonReplay.toOccurrence.trace.length :=
  ⟨2, by decide⟩

def positiveSingletonStone : OccupiedStone
    ((oppositeSingletonReplay.toOccurrence.trace.get
      oppositeSingletonTime).visible.board) where
  point := p00
  polarity := .positive
  occupied := by decide

def negativeSingletonStone : OccupiedStone
    ((oppositeSingletonReplay.toOccurrence.trace.get
      oppositeSingletonTime).visible.board) where
  point := p22
  polarity := .negative
  occupied := by decide

def positiveSingletonNode : ReplaySnapshotGroup oppositeSingletonReplay where
  time := oppositeSingletonTime
  group := snapshotGroupOf positiveSingletonStone

def negativeSingletonNode : ReplaySnapshotGroup oppositeSingletonReplay where
  time := oppositeSingletonTime
  group := snapshotGroupOf negativeSingletonStone

/-- Equal-cardinality singleton shapes of opposite generated polarity cannot
be merged by a name or presentation: persistent identity requires exact
same-stone replay lineage. -/
theorem persistent_lookalike_wrong_lineage :
    positiveSingletonNode.group.carrier.card =
        negativeSingletonNode.group.carrier.card ∧
      generatedGroupIdentityOf positiveSingletonNode ≠
        generatedGroupIdentityOf negativeSingletonNode := by
  constructor
  · decide
  · apply generatedGroupIdentity_ne_of_polarity_ne
    decide

/-! ## Whole capture on the exact 2×2 replay -/

def q00 : Point 2 := (0, 0)
def q01 : Point 2 := (0, 1)
def q10 : Point 2 := (1, 0)
def q11 : Point 2 := (1, 1)

def capturePrefixMoves : List (Move 2) :=
  [.play q00, .play q01, .play q10]

theorem capturePrefix_generated_isSome :
    (generate? zeroKomiLaw 2 capturePrefixMoves).isSome = true := by
  decide

def capturePrefixReplay :
    GeneratedReplay zeroKomiLaw (Frame.initial 2) capturePrefixMoves :=
  (generate? zeroKomiLaw 2 capturePrefixMoves).get
    capturePrefix_generated_isSome

theorem capturingMove_generated_isSome :
    (nativeStep? zeroKomiLaw capturePrefixReplay.final (.play q11)).isSome = true := by
  decide

def captureTarget : Frame 2 :=
  (nativeStep? zeroKomiLaw capturePrefixReplay.final (.play q11)).get
    capturingMove_generated_isSome

theorem captureStep :
    LegalStep zeroKomiLaw capturePrefixReplay.final (.play q11) captureTarget := by
  unfold LegalStep
  decide

def capturePly : GeneratedReplay.ActualPly capturePrefixReplay where
  target := captureTarget
  emitted := .play q11
  step := captureStep

def capturedSourceStone :
    OccupiedStone capturePrefixReplay.final.visible.board where
  point := q00
  polarity := .positive
  occupied := by decide

/-- The old two-stone positive component receives a whole-carrier terminal
disposition at the exact generated target. -/
def capturedGroupTerminal :
    ActualCaptureTerminalDisposition capturePly :=
  actualCaptureTerminal_of_carrier_subset_captured capturePly q11 rfl
    (snapshotGroupOf capturedSourceStone) (by
    change ∀ point ∈ groupAt capturePrefixReplay.final.visible.board q00,
      point ∈ capturedStonesAfterPlay
        capturePrefixReplay.final.visible.board
        capturePrefixReplay.final.visible.toMove q11
    decide
  )

theorem captured_group_carrier_is_exact :
    capturedGroupTerminal.source.carrier = {q00, q10} := by
  decide

/-- Terminal capture forbids every same-stone outgoing group transport. -/
theorem captured_group_has_no_successor
    (targetGroup : SnapshotGroup captureTarget.visible.board) :
    ¬ ActualExactGroupTransport capturePly capturedGroupTerminal.source
      targetGroup :=
  capturedGroupTerminal.noExactTransport targetGroup

theorem capture_carrier_successor_coherent :
    CarrierSuccessorCoherent capturePrefixReplay.final.visible.board
      captureTarget.visible.board := by
  decide

theorem capture_actual_split_isEmpty :
    IsEmpty (ActualSplitDisposition capturePly) :=
  actualSplitDisposition_isEmpty_of_sourceSuccessorCoherent capturePly
    (sourceSuccessorCoherent_of_carrier capture_carrier_successor_coherent)

/-! ## Generic split transporter versus actual Go authority -/

/-- Removing only the bridge produces two descendants as a generic board
relation.  It is deliberately not called an actual Go step. -/
def splitCandidateBoard : Board 3 :=
  Board.set bridgeTarget.visible.board p01 none

def splitLeft : SurvivingStone bridgeTarget.visible.board splitCandidateBoard where
  point := p00
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

def splitRight : SurvivingStone bridgeTarget.visible.board splitCandidateBoard where
  point := p02
  polarity := .positive
  before_occupied := by decide
  after_occupied := by decide

def genericBridgeSplit :
    SplitDisposition bridgeTarget.visible.board splitCandidateBoard where
  left := splitLeft
  right := splitRight
  commonSource := by
    apply SnapshotGroup.eq_iff_carrier_eq.mpr
    decide
  distinctTargets := by
    intro equalGroups
    have equalCarriers := SnapshotGroup.eq_iff_carrier_eq.mp equalGroups
    change groupAt splitCandidateBoard p00 =
      groupAt splitCandidateBoard p02 at equalCarriers
    have distinctCarriers :
        groupAt splitCandidateBoard p00 ≠
          groupAt splitCandidateBoard p02 := by
      decide
    exact distinctCarriers equalCarriers

theorem genericBridgeSplit_two_exact_descendants :
    ExactGroupTransport genericBridgeSplit.left.sourceGroup
        genericBridgeSplit.leftDescendant ∧
      ExactGroupTransport genericBridgeSplit.left.sourceGroup
        genericBridgeSplit.rightDescendant ∧
      genericBridgeSplit.leftDescendant ≠
        genericBridgeSplit.rightDescendant :=
  ⟨genericBridgeSplit.left_exactTransport,
    genericBridgeSplit.right_exactTransport,
    genericBridgeSplit.descendants_distinct⟩

/-- Exhaustive finite compilation rejects the forged partial-split board as
the next board of every move from the reachable current.  Thus the split
transporter is available for more general relation groups, but it carries no
actual Go occurrence authority. -/
theorem genericBridgeSplit_has_no_actual_move :
    ∀ move : Move 3,
      (nativeStep? zeroKomiLaw bridgeTarget move).map
          (fun frame => boardSignature frame.visible.board) ≠
        some (boardSignature splitCandidateBoard) := by
  intro move
  cases move with
  | play point =>
      rcases point with ⟨row, column⟩
      fin_cases row <;> fin_cases column <;> decide
  | pass => decide
  | resign => decide

end G2GroupLineageRegression
end Go
end ProcessGame
end SaturationMonoid
