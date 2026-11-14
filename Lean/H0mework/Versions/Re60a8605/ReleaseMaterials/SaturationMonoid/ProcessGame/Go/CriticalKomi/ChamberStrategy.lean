import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoPointChamber
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoPointChamber

open TwoEye

/-- One observed placement is enough to compile the permanent enlarged area closure. -/
def sealCertificate {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} (frame : Frame n) (playing : frame.visible.status = .playing)
    (owned : frame.visible.toMove = colour) (inside : TwoEye.Holds g colour frame.visible.board)
    (first : frame.visible.board chamber.first = none ∨
      frame.visible.board chamber.first = some colour.other)
    (empty : frame.visible.board chamber.second = none)
    (virgin : Growth.Virgin g colour chamber.second frame.positionHistory) :
    Certificate colour (bound g colour) frame :=
  let response := captureReply chamber frame playing owned inside empty virgin
  let detected : TwoEyeFamily.Detected response.target.visible.board colour :=
    ⟨securedFamily chamber, seal_secures chamber inside first empty⟩
  have relaxed : acceptsMargin colour (bound g colour) detected.bound = true := by
    change acceptsMargin colour (bound g colour)
      (TwoEyeFamily.bound (securedFamily chamber) colour) = true
    rw [secured_bound chamber inside first empty]
    cases colour <;> simp [acceptsMargin]
  .choose owned response (.twoEyeFamily detected
    (nonresigning_step_scoringStatus response.notResign response.step) relaxed)

private theorem play_board_turn {n : Nat} {frame target : Frame n} {played : Point n}
    (step : LegalStep (Law.positionalSuperko 0) frame (.play played) target) :
    target.visible.board = boardAfterPlay frame.visible.board frame.visible.toMove played ∧
      target.visible.toMove = frame.visible.toMove.other := by
  have generated := nativeStep_visible_eq step
  simp only [stepVisible?, playVisible?] at generated
  split at generated
  · simp at generated
  · split at generated
    · split at generated
      · split at generated
        · simp at generated
        · have same := Option.some.inj generated
          rw [← same]
          exact ⟨rfl, rfl⟩
      · simp at generated
    · simp at generated

private theorem pass_turn {n : Nat} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko 0) frame .pass target) :
    target.visible.toMove = frame.visible.toMove.other := by
  have generated := nativeStep_visible_eq step
  simp only [stepVisible?, passVisible?] at generated
  split at generated
  · simp at generated
  · simp only [Law.positionalSuperko, reduceCtorEq, false_and, ↓reduceIte] at generated
    exact (congrArg VisiblePosition.toMove (Option.some.inj generated)).symm

/-- The response is chosen after the opponent's actual native step.  Every
possible placement, capture elsewhere, and exempt pass uses the same source relation. -/
def afterOpponent {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} {frame target : Frame n} {move : Move n}
    (inside : TwoEye.Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other)
    (passes : frame.visible.consecutivePasses = 0)
    (firstEmpty : frame.visible.board chamber.first = none)
    (secondEmpty : frame.visible.board chamber.second = none)
    (firstVirgin : Growth.Virgin g colour chamber.first frame.positionHistory)
    (secondVirgin : Growth.Virgin g colour chamber.second frame.positionHistory)
    (scoring : move ≠ .resign) (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    Certificate colour (bound g colour) target := by
  have preserved := TwoEye.opponent_legalStep_preserves inside opponent scoring step
  cases move with
  | resign => exact False.elim (scoring rfl)
  | pass =>
      have facts := pass_step_facts step
      have playing : target.visible.status = .playing := by
        simpa only [passes, Nat.zero_add, show ¬ 2 ≤ (1 : Nat) from by omega, ↓reduceIte]
          using facts.2.2.2
      have owned : target.visible.toMove = colour := by
        rw [pass_turn step, opponent, Polarity.other_other]
      have first : target.visible.board chamber.first = none := by rw [facts.2.1]; exact firstEmpty
      have second : target.visible.board chamber.second = none := by rw [facts.2.1]; exact secondEmpty
      exact sealCertificate chamber target playing owned preserved (.inl first) second
        (Growth.virgin_step secondVirgin step (by rw [second]; simp))
  | play played =>
      have facts := play_board_turn step
      have playing := (play_step_facts step).2.1
      have owned : target.visible.toMove = colour := by
        rw [facts.2, opponent, Polarity.other_other]
      have boardEq : target.visible.board = boardAfterPlay frame.visible.board colour.other played := by
        rw [facts.1, opponent]
      if atFirst : played = chamber.first then
        have invader : target.visible.board chamber.first = some colour.other := by
          rw [boardEq, atFirst]
          exact Growth.placed_survives _ _ _
        have second : target.visible.board chamber.second = none := by
          rw [boardEq, atFirst]
          exact unplayed_empty secondEmpty chamber.distinct.symm
        exact sealCertificate chamber target playing owned preserved (.inr invader) second
          (Growth.virgin_step secondVirgin step (by rw [second]; simp))
      else if atSecond : played = chamber.second then
        have invader : target.visible.board chamber.second = some colour.other := by
          rw [boardEq, atSecond]
          exact Growth.placed_survives _ _ _
        have first : target.visible.board chamber.first = none := by
          rw [boardEq, atSecond]
          exact unplayed_empty firstEmpty chamber.distinct
        exact sealCertificate chamber.swap target playing owned preserved (.inr invader) first
          (Growth.virgin_step firstVirgin step (by change target.visible.board chamber.first ≠ _; rw [first]; simp))
      else
        have first : target.visible.board chamber.first = none := by
          rw [boardEq]
          exact unplayed_empty firstEmpty (Ne.symm atFirst)
        have second : target.visible.board chamber.second = none := by
          rw [boardEq]
          exact unplayed_empty secondEmpty (Ne.symm atSecond)
        exact sealCertificate chamber target playing owned preserved (.inl first) second
          (Growth.virgin_step secondVirgin step (by rw [second]; simp))

/-- Two empty source cells add two guaranteed area points even when the opponent moves first. -/
def opponentCertificate {n : Nat} {g : TwoEye.Geometry n} (chamber : Geometry g)
    {colour : Polarity} (frame : Frame n) (playing : frame.visible.status = .playing)
    (inside : TwoEye.Holds g colour frame.visible.board)
    (opponent : frame.visible.toMove = colour.other) (passes : frame.visible.consecutivePasses = 0)
    (firstEmpty : frame.visible.board chamber.first = none)
    (secondEmpty : frame.visible.board chamber.second = none)
    (firstVirgin : Growth.Virgin g colour chamber.first frame.positionHistory)
    (secondVirgin : Growth.Virgin g colour chamber.second frame.positionHistory) :
    Certificate colour (bound g colour) frame :=
  .all playing (by rw [opponent]; exact Polarity.other_ne colour) (fun port =>
    have native := mem_scoringExpansion_iff.mp (List.get_mem (scoringExpansion frame) port)
    afterOpponent chamber inside opponent passes firstEmpty secondEmpty
      firstVirgin secondVirgin native.2 native.1)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoPointChamber
