import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.HistoryKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ScoreReadout
import Mathlib.Tactic.NormNum

/-!
# G1 rules and replay regression

Concrete 1×1 and 2×2 source scripts exercise placement, capture, suicide,
explicit pass repetition, two-pass terminality, resignation, area score, native
position-history write-back and the shared occurrence fold.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G1RulesRegression

def halfKomiLaw : Law := Law.positionalSuperko (1 / 2)

def strictPassLaw : Law where
  repetition := .positionalSuperko
  passRepetition := .subjectToPositionalSuperko
  komi := 0

def p00 : Point 2 := (0, 0)
def p01 : Point 2 := (0, 1)
def p10 : Point 2 := (1, 0)
def p11 : Point 2 := (1, 1)

def preCaptureMoves : List (Move 2) :=
  [.play p00, .play p01, .play p10]

theorem preCapture_generated_isSome :
    (generate? halfKomiLaw 2 preCaptureMoves).isSome = true := by
  decide

def preCaptureReplay :
    GeneratedReplay halfKomiLaw (Frame.initial 2) preCaptureMoves :=
  (generate? halfKomiLaw 2 preCaptureMoves).get preCapture_generated_isSome

/-- The fourth move generates one exact two-stone capture set. -/
theorem fourth_move_captures_left_group :
    capturedStonesAfterPlay preCaptureReplay.final.visible.board .negative p11 =
      {p00, p10} := by
  decide

def completeMoves : List (Move 2) :=
  preCaptureMoves ++ [.play p11, .pass, .pass]

theorem completeReplay_generated_isSome :
    (generate? halfKomiLaw 2 completeMoves).isSome = true := by
  decide

def completeReplay :
    GeneratedReplay halfKomiLaw (Frame.initial 2) completeMoves :=
  (generate? halfKomiLaw 2 completeMoves).get completeReplay_generated_isSome

/-- Capture removes both positive stones and preserves both negative stones. -/
theorem completeReplay_capture_board :
    completeReplay.final.visible.board p00 = none ∧
      completeReplay.final.visible.board p10 = none ∧
      completeReplay.final.visible.board p01 = some .negative ∧
      completeReplay.final.visible.board p11 = some .negative := by
  decide

/-- Two consecutive generated passes close the local game. -/
theorem completeReplay_two_pass_terminal :
    completeReplay.final.visible.consecutivePasses = 2 ∧
      completeReplay.final.visible.status = .terminal .twoPasses := by
  decide

/-- Chinese area gives the negative polarity all four points; half-point komi
therefore yields margin `-9/2`. -/
theorem completeReplay_area_margin :
    scoreMargin halfKomiLaw completeReplay.final.visible.board = -(9 / 2) := by
  have positive_area :
      areaScore completeReplay.final.visible.board .positive = 0 := by
    decide
  have negative_area :
      areaScore completeReplay.final.visible.board .negative = 4 := by
    decide
  rw [scoreMargin, positive_area, negative_area]
  change (0 : ℚ) - 4 - (1 / 2) = -(9 / 2)
  norm_num

def onlyPoint : Point 1 := (0, 0)

/-- A 1×1 placement has no post-capture liberty and is rejected as suicide. -/
theorem one_by_one_suicide_rejected :
    nativeStep? halfKomiLaw (Frame.initial 1) (.play onlyPoint) = none := by
  decide

/-- The authoritative positional-superko law explicitly exempts pass. -/
theorem exempt_pass_is_generated :
    (nativeStep? halfKomiLaw (Frame.initial 1) (.pass : Move 1)).isSome = true := by
  decide

/-- The strict pass branch subjects the unchanged board to positional superko
and therefore rejects the same initial pass. -/
theorem strict_pass_repetition_rejected :
    nativeStep? strictPassLaw (Frame.initial 1) (.pass : Move 1) = none := by
  decide

theorem resignation_generated_isSome :
    (nativeStep? halfKomiLaw (Frame.initial 1) (.resign : Move 1)).isSome = true := by
  decide

def resignationTarget : Frame 1 :=
  (nativeStep? halfKomiLaw (Frame.initial 1) (.resign : Move 1)).get
    resignation_generated_isSome

/-- Resignation generates the opposing polarity as winner. -/
theorem resignation_generates_terminal_winner :
    resignationTarget.visible.status = .terminal (.resignation .negative) := by
  decide

/-- The final superko prefix is exactly the same occurrence's situation
trace; the test never constructs a seen-set. -/
theorem completeReplay_history_is_occurrence_trace :
    completeReplay.toOccurrence.trace.map
        (fun frame => frame.visible.situation) =
      completeReplay.final.positionHistory :=
  generated_occurrence_situations_eq_positionHistory completeReplay

/-- Visible replay is the existing one-constructor occurrence fold. -/
theorem completeReplay_visible_is_occurrence_fold :
    (completeReplay.toOccurrence.fold GeneratedReplay.finalAlgebra).visible =
      completeReplay.final.visible :=
  generated_occurrence_fold_visible_eq_replay completeReplay

end G1RulesRegression
end Go
end ProcessGame
end SaturationMonoid
