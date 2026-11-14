import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CalculationRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialBoundReceiptControl

open GoalBracket

def playedPolicy : ExecutablePolicy 19 where
  reply frame playing :=
    match generated : nativeStep? (Law.positionalSuperko 0) frame (.play (0,0)) with
    | some target => ⟨.play (0,0), target, by simp, generated⟩
    | none => passReply frame playing

def blackBound (value : Int) (bounded : value ≤ -361) : InitialBound where
  colour := .positive
  value := value
  policy := playedPolicy
  guarantee opponent := by
    have area := TwoEye.Score.black_margin_bound
      (initialPlay 19 (versus .positive playedPolicy opponent)).replay.final.visible.board
      0 (Nat.zero_le _)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, zero_sub] at area
    simpa only [acceptsMargin, decide_eq_true_eq] using (Int.le_trans bounded area)

def whiteBound (value : Int) (bounded : 361 ≤ value) : InitialBound where
  colour := .negative
  value := value
  policy := playedPolicy
  guarantee opponent := by
    have area := TwoEye.Score.white_margin_bound
      (initialPlay 19 (versus .negative playedPolicy opponent)).replay.final.visible.board
      0 (Nat.zero_le _)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at area
    simpa only [acceptsMargin, decide_eq_true_eq] using (Int.le_trans area bounded)

def wide : Bracket where
  lower := -400
  upper := 400
  white := initial.white
  black := initial.black
  black_guarantee opponent :=
    Int.le_trans (show (-400 : Int) ≤ -361 by decide) (initial.black_guarantee opponent)
  white_guarantee opponent :=
    Int.le_trans (initial.white_guarantee opponent) (show (361 : Int) ≤ 400 by decide)

def source : GoalCursor.State := {
  bracket := wide
  queryThreshold := wide.cut
  query := DecisionCursor.initial19 wide.cut
  query_valid := by right; constructor <;> decide
}

private def next (current : GoalCursor.State) : IO GoalCursor.State := do
  let event := CalculationRuntime.authoritativeRoot.toRoot.evolutionAt (.calculating current)
  unless (CalculationRuntime.writeRows current).size == 1 do
    throw (IO.userError "a received bound changed the original single responsibility row")
  match event.nextCurrent? with
  | some (.calculating target) => pure target
  | _ => throw (IO.userError "this bound receipt unexpectedly terminated the original calculation")

example (current : GoalCursor.State) (bound : InitialBound)
    (stable : ¬ bound.Improves current.bracket) :
    GoalCursor.absorb current bound = .inr current :=
  GoalCursor.absorb_not_improving current bound stable

example (visit : CalculationRuntime.Visit) :
    HEq (CalculationRuntime.faceAt visit .mathematicalBounds)
      (CalculationRuntime.projectionLaw.outcomeAt .mathematicalBounds
        (CalculationRuntime.emitted visit.current)) :=
  CalculationRuntime.mathematicalAt_authority visit

def run : IO Unit := do
  let started ← IO.monoMsNow
  let black := blackBound (-361) (by decide)
  let white := whiteBound 361 (by decide)
  let queued := (source.receive black).receive white
  let first ← next queued
  unless first.bracket.lower == -361 && first.bracket.upper == 400 &&
      first.bracket.cut == 19 && first.received.length == 1 &&
      (first.bracket.black.reply (Frame.initial 19) rfl).move == .play (0,0) &&
      (first.bracket.white.reply (Frame.initial 19) rfl).move == .pass do
    throw (IO.userError "the arbitrary Black bound lost its policy, opposite side, next cut, or later receipt")
  let second ← next first
  unless second.bracket.lower == -361 && second.bracket.upper == 361 &&
      second.bracket.cut == 0 && second.received.isEmpty &&
      (second.bracket.white.reply (Frame.initial 19) rfl).move == .play (0,0) &&
      (second.bracket.black.reply (Frame.initial 19) rfl).move == .play (0,0) do
    throw (IO.userError "the arbitrary White bound failed to retain both actual policies")
  let weaker ← next (GoalCursor.initial.receive (blackBound (-400) (by decide)))
  let equal ← next (GoalCursor.initial.receive black)
  for target in [weaker, equal] do
    unless target.bracket.lower == -361 && target.bracket.upper == 361 &&
        (target.bracket.black.reply (Frame.initial 19) rfl).move == .pass &&
        target.received.isEmpty do
      throw (IO.userError "a non-improving receipt replaced the paid strategy or survived consumption")
  let limits := CalculationRuntime.mathematicalAt CalculationRuntime.seed
  unless limits.lower == 0 && limits.upper == 361 do
    throw (IO.userError "the same-root mathematical bounds changed")
  let visit := CalculationRuntime.observe 1
  match visit.current with
  | .calculating current =>
      unless current.bracket.lower == -361 && current.bracket.upper == 361 do
        throw (IO.userError "mathematical existence changed the executable seed ledger")
  | .solved _ => throw (IO.userError "the original seed was falsely reported solved")
  IO.println s!"same-source single-row receipt controls passed: arbitrary Black/White bounds, stored executable policies, next cuts, retained later receipt, weaker/equal rejection; mathematical [0,361] and executable seed [-361,361]; {(← IO.monoMsNow)-started} ms"

end SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialBoundReceiptControl

def main : IO Unit := SaturationMonoid.ProcessGame.Go.CriticalKomi.InitialBoundReceiptControl.run
