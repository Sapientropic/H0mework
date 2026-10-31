import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.HistoryKernel

/-!
# Reachable ko/fresh path pair

Two legal 2×2 source scripts reach the same visible position.  One script has
already visited the board produced by the next capture; the other has not.
Positional superko therefore rejects the capture only on the first history.
This production module fixes the two exact actual replays for downstream
cross-occurrence consumers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G1HistoryCounterexample

def law : Law := Law.positionalSuperko 0

def p00 : Point 2 := (0, 0)
def p01 : Point 2 := (0, 1)
def p10 : Point 2 := (1, 0)
def p11 : Point 2 := (1, 1)

/-- This history visits the singleton-positive board before the stone is later
captured. -/
def koMoves : List (Move 2) :=
  [.play p00, .play p11, .pass, .play p10, .pass, .play p01]

/-- This history uses a first pass and never visits the singleton-positive
board. -/
def freshMoves : List (Move 2) :=
  [.pass, .play p11, .pass, .play p10, .pass, .play p01]

theorem koReplay_generated_isSome :
    (generate? law 2 koMoves).isSome = true := by
  decide

theorem freshReplay_generated_isSome :
    (generate? law 2 freshMoves).isSome = true := by
  decide

def koReplay : GeneratedReplay law (Frame.initial 2) koMoves :=
  (generate? law 2 koMoves).get koReplay_generated_isSome

def freshReplay : GeneratedReplay law (Frame.initial 2) freshMoves :=
  (generate? law 2 freshMoves).get freshReplay_generated_isSome

/-- Board, side to move, pass count and status are all identical. -/
theorem final_visible_eq :
    koReplay.final.visible = freshReplay.final.visible := by
  apply VisiblePosition.ext
  · apply boardSignature_injective
    decide
  · decide
  · decide
  · decide

/-- The occurrence-generated positional histories remain different. -/
theorem final_positionHistory_ne :
    koReplay.final.positionHistory ≠ freshReplay.final.positionHistory := by
  decide

/-- Capturing at `p00` would recreate a board in the first actual history. -/
theorem ko_recapture_rejected :
    nativeStep? law koReplay.final (.play p00) = none := by
  decide

theorem fresh_recapture_isSome :
    (nativeStep? law freshReplay.final (.play p00)).isSome = true := by
  decide

def freshRecaptureTarget : Frame 2 :=
  (nativeStep? law freshReplay.final (.play p00)).get fresh_recapture_isSome

theorem fresh_recapture_legal :
    LegalMove law freshReplay.final (.play p00) := by
  refine ⟨freshRecaptureTarget, ?_⟩
  exact (Option.some_get fresh_recapture_isSome).symm

theorem ko_recapture_not_legal :
    ¬ LegalMove law koReplay.final (.play p00) := by
  rintro ⟨target, generated⟩
  unfold LegalStep at generated
  rw [ko_recapture_rejected] at generated
  cases generated

/-- Reachable equal visible positions have different legal-move fibres. -/
theorem reachable_sameVisible_differentLegalMoves :
    koReplay.final.visible = freshReplay.final.visible ∧
      ¬ LegalMove law koReplay.final (.play p00) ∧
      LegalMove law freshReplay.final (.play p00) :=
  ⟨final_visible_eq, ko_recapture_not_legal, fresh_recapture_legal⟩

/-- Both histories' superko prefixes remain exact projections of their own
shared-root actual occurrences. -/
theorem histories_are_occurrence_projections :
    koReplay.toOccurrence.trace.map (fun frame => frame.visible.situation) =
        koReplay.final.positionHistory ∧
      freshReplay.toOccurrence.trace.map (fun frame => frame.visible.situation) =
        freshReplay.final.positionHistory :=
  ⟨generated_occurrence_situations_eq_positionHistory koReplay,
    generated_occurrence_situations_eq_positionHistory freshReplay⟩

end G1HistoryCounterexample
end Go
end ProcessGame
end SaturationMonoid
