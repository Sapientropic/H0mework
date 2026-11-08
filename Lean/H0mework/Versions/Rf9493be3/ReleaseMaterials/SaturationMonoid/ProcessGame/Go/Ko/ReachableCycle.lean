import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.RootedOccurrence

/-!
# Reachable lifted ko cycle

One 3×3 script realizes the same local ko-pattern loop under simple ko,
positional superko and situational superko.  A remote threat prevents the
lifted board from repeating, while the exact replay history records the
different occurrence.  The script is assembled from one generated setup and
four shared one-ply continuations; no whole-game search or completed future is
stored here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace KoReachableCycle

def p00 : Point 3 := (0, 0)
def p01 : Point 3 := (0, 1)
def p02 : Point 3 := (0, 2)
def p10 : Point 3 := (1, 0)
def p11 : Point 3 := (1, 1)
def p22 : Point 3 := (2, 2)

/-- The common rules differ only in repetition semantics. -/
def law (rule : RepetitionRule) : Law where
  repetition := rule
  passRepetition := .exempt
  komi := 0

def setupMoves : List (Move 3) :=
  [.pass, .play p00, .play p10, .play p02, .pass, .play p11]

def captureMove : Move 3 := .play p01
def threatMove : Move 3 := .play p22
def answerPass : Move 3 := .pass
def recaptureMove : Move 3 := .play p00

def afterCaptureMoves : List (Move 3) := setupMoves ++ [captureMove]
def afterThreatMoves : List (Move 3) := afterCaptureMoves ++ [threatMove]
def beforeRecaptureMoves : List (Move 3) := afterThreatMoves ++ [answerPass]
def cycleMoves : List (Move 3) := beforeRecaptureMoves ++ [recaptureMove]

theorem setup_generated_isSome (rule : RepetitionRule) :
    (generate? (law rule) 3 setupMoves).isSome = true := by
  cases rule <;> decide

/-- Exact reachable current immediately before the ko capture. -/
def setupReplay (rule : RepetitionRule) :
    GeneratedReplay (law rule) (Frame.initial 3) setupMoves :=
  (generate? (law rule) 3 setupMoves).get (setup_generated_isSome rule)

private def actualPlyOfIsSome {rule : RepetitionRule}
    {moves : List (Move 3)}
    (replay : GeneratedReplay (law rule) (Frame.initial 3) moves)
    (move : Move 3)
    (generated : (nativeStep? (law rule) replay.final move).isSome = true) :
    GeneratedReplay.ActualPly replay where
  target := (nativeStep? (law rule) replay.final move).get generated
  emitted := move
  step := by
    unfold LegalStep
    exact (Option.some_get generated).symm

theorem capture_target_isSome (rule : RepetitionRule) :
    (nativeStep? (law rule) (setupReplay rule).final captureMove).isSome =
      true := by
  cases rule <;> decide

def capturePly (rule : RepetitionRule) :
    GeneratedReplay.ActualPly (setupReplay rule) :=
  actualPlyOfIsSome (setupReplay rule) captureMove
    (capture_target_isSome rule)

def afterCaptureReplay (rule : RepetitionRule) :=
  (capturePly rule).extended

theorem threat_target_isSome (rule : RepetitionRule) :
    (nativeStep? (law rule) (afterCaptureReplay rule).final threatMove).isSome =
      true := by
  cases rule <;> decide

def threatPly (rule : RepetitionRule) :
    GeneratedReplay.ActualPly (afterCaptureReplay rule) :=
  actualPlyOfIsSome (afterCaptureReplay rule) threatMove
    (threat_target_isSome rule)

def afterThreatReplay (rule : RepetitionRule) :=
  (threatPly rule).extended

theorem answer_pass_target_isSome (rule : RepetitionRule) :
    (nativeStep? (law rule) (afterThreatReplay rule).final answerPass).isSome =
      true := by
  cases rule <;> decide

def answerPassPly (rule : RepetitionRule) :
    GeneratedReplay.ActualPly (afterThreatReplay rule) :=
  actualPlyOfIsSome (afterThreatReplay rule) answerPass
    (answer_pass_target_isSome rule)

def beforeRecaptureReplay (rule : RepetitionRule) :=
  (answerPassPly rule).extended

theorem recapture_target_isSome (rule : RepetitionRule) :
    (nativeStep? (law rule) (beforeRecaptureReplay rule).final
      recaptureMove).isSome = true := by
  cases rule <;> decide

def recapturePly (rule : RepetitionRule) :
    GeneratedReplay.ActualPly (beforeRecaptureReplay rule) :=
  actualPlyOfIsSome (beforeRecaptureReplay rule) recaptureMove
    (recapture_target_isSome rule)

/-- Full exact lifted cycle, still indexed by its generated move spine. -/
def cycleReplay (rule : RepetitionRule) :=
  (recapturePly rule).extended

def simpleCycleReplay := cycleReplay .simpleKo
def positionalCycleReplay := cycleReplay .positionalSuperko
def situationalCycleReplay := cycleReplay .situationalSuperko

/-- The visible restriction which forgets the remote threat and history. -/
abbrev LocalKoProjection := List (Option Polarity) × Polarity

def localProjection (frame : Frame 3) : LocalKoProjection :=
  ([frame.visible.board p00, frame.visible.board p01,
    frame.visible.board p02, frame.visible.board p10,
    frame.visible.board p11], frame.visible.toMove)

/-- Capture and delayed recapture close the local pattern for every required
repetition law. -/
theorem local_projection_loop (rule : RepetitionRule) :
    localProjection (setupReplay rule).final =
      localProjection (cycleReplay rule).final := by
  cases rule <;> decide

theorem setup_remote_threat_empty (rule : RepetitionRule) :
    (setupReplay rule).final.visible.board p22 = none := by
  cases rule <;> decide

theorem cycle_remote_threat_present (rule : RepetitionRule) :
    (cycleReplay rule).final.visible.board p22 = some .negative := by
  cases rule <;> decide

/-- The lifted boards differ even though the local projection closes. -/
theorem global_board_ne (rule : RepetitionRule) :
    (setupReplay rule).final.visible.board ≠
      (cycleReplay rule).final.visible.board := by
  intro equalBoards
  have pointEqual := congrArg (fun board => board p22) equalBoards
  rw [setup_remote_threat_empty rule,
    cycle_remote_threat_present rule] at pointEqual
  cases pointEqual

theorem setup_history_length (rule : RepetitionRule) :
    (setupReplay rule).final.positionHistory.length = 7 := by
  cases rule <;> decide

theorem cycle_history_length (rule : RepetitionRule) :
    (cycleReplay rule).final.positionHistory.length = 11 := by
  cases rule <;> decide

/-- The local loop is not a lifted occurrence loop: its generated histories
have different lengths and hence are distinct. -/
theorem lifted_history_ne (rule : RepetitionRule) :
    (setupReplay rule).final.positionHistory ≠
      (cycleReplay rule).final.positionHistory := by
  intro equalHistories
  have lengthEqual := congrArg List.length equalHistories
  rw [setup_history_length rule, cycle_history_length rule] at lengthEqual
  omega

/-- Immediate recapture returns the preceding full board and is rejected by
all three repetition semantics. -/
theorem immediate_recapture_rejected (rule : RepetitionRule) :
    nativeStep? (law rule) (afterCaptureReplay rule).final recaptureMove =
      none := by
  cases rule <;> decide

theorem immediate_recapture_not_legal (rule : RepetitionRule) :
    ¬ LegalMove (law rule) (afterCaptureReplay rule).final recaptureMove := by
  rintro ⟨target, step⟩
  unfold LegalStep at step
  rw [immediate_recapture_rejected rule] at step
  cases step

/-- The remote threat plus one exempt answering pass makes the exact
recapture a legal compiler image. -/
theorem delayed_recapture_legal (rule : RepetitionRule) :
    LegalMove (law rule) (beforeRecaptureReplay rule).final recaptureMove :=
  ⟨(recapturePly rule).target, (recapturePly rule).step⟩

theorem delayed_recapture_mem_expansion (rule : RepetitionRule) :
    (recaptureMove, (recapturePly rule).target) ∈
      legalExpansion (law rule) (beforeRecaptureReplay rule).final :=
  actualPly_mem_legalExpansion (recapturePly rule)

theorem threat_not_replayable_when_occupied (rule : RepetitionRule) :
    nativeStep? (law rule) (beforeRecaptureReplay rule).final threatMove =
      none := by
  cases rule <;> decide

theorem threat_is_frontier_before_play (rule : RepetitionRule) :
    LegalMove (law rule) (afterCaptureReplay rule).final threatMove :=
  ⟨(threatPly rule).target, (threatPly rule).step⟩

theorem threat_is_absent_after_play (rule : RepetitionRule) :
    ¬ LegalMove (law rule) (beforeRecaptureReplay rule).final threatMove := by
  rintro ⟨target, step⟩
  unfold LegalStep at step
  rw [threat_not_replayable_when_occupied rule] at step
  cases step

theorem after_capture_ko_stone_present (rule : RepetitionRule) :
    (afterCaptureReplay rule).final.visible.board p01 = some .positive := by
  cases rule <;> decide

/-- Exact generated stone whose snapshot group is born at the capture. -/
def capturedKoStone (rule : RepetitionRule) :
    OccupiedStone (afterCaptureReplay rule).final.visible.board where
  point := p01
  polarity := .positive
  occupied := after_capture_ko_stone_present rule

def capturedKoGroup (rule : RepetitionRule) :
    SnapshotGroup (afterCaptureReplay rule).final.visible.board :=
  snapshotGroupOf (capturedKoStone rule)

end KoReachableCycle
end Go
end ProcessGame
end SaturationMonoid
