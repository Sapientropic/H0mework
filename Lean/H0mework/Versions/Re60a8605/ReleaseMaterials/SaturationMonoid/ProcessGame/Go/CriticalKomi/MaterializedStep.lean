import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionalProgram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep

/-- Reuse the same actual capture matrix for liberty, repetition and history
readers. Every original rule guard is retained. -/
def play? (law : Law) (frame : Frame 19) (point : Point 19) : Option (VisiblePosition 19) :=
  match frame.visible.status with
  | .terminal _ => none
  | .playing =>
      if frame.visible.board point = none then
        let effect := RegionalProgram.capturePlayEffect frame.visible.board frame.visible.toMove point
        if stoneHasLiberty effect.board point then
          let nextToMove := frame.visible.toMove.other
          if violatesRepetition law.repetition frame.positionHistory
              { board := boardSignature effect.board, toMove := nextToMove } then
            none
          else some {
            board := effect.board
            toMove := nextToMove
            consecutivePasses := 0
            status := .playing }
        else none
      else none

theorem play_eq (law : Law) (frame : Frame 19) (point : Point 19) :
    play? law frame point = playVisible? law frame point := by
  cases status : frame.visible.status <;>
    simp only [play?, playVisible?, status, RegionalProgram.PlayEffect.board_eq]

def step? (law : Law) (frame : Frame 19) (move : Move 19) : Option (Frame 19) :=
  let visible := match move with
    | .play point => play? law frame point
    | .pass => passVisible? law frame
    | .resign => resignVisible? frame
  visible.map (Frame.advance frame)

theorem step_eq (law : Law) (frame : Frame 19) (move : Move 19) :
    step? law frame move = nativeStep? law frame move := by
  cases move <;> simp only [step?, nativeStep?, stepVisible?, play_eq]

def scoring (frame : Frame 19) : List (Move 19 × Frame 19) :=
  ((allMoves 19).filterMap fun move =>
    (step? (Law.positionalSuperko 0) frame move).map (fun target => (move, target))).filter
      (fun child => child.1 ≠ .resign)

theorem scoring_eq (frame : Frame 19) : scoring frame = scoringExpansion frame := by
  simp only [scoring, scoringExpansion, legalExpansion, step_eq]

end SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep
