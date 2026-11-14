import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.HistoryKernel
import Mathlib.Data.Finset.Card

/-!
# Strict progress of the original positional-superko Go process

This subordinate producer reads the board prefix written by `nativeStep?`.
Each legal placement spends a fresh board; an exempt pass spends the remaining
pass phase or generates the actual two-pass terminal.  The finite rank is used
only for well-founded proofs, with no evaluation of the board universe.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

/-- Board positions that the native repetition prefix has not yet recorded. -/
def unseenBoards {n : Nat} (frame : Frame n) : Finset (Board n) :=
  Finset.univ.filter (fun board =>
    ¬ ∃ previous ∈ frame.positionHistory, previous.board = boardSignature board)

@[simp] theorem mem_unseenBoards {n : Nat} (frame : Frame n) (board : Board n) :
    board ∈ unseenBoards frame ↔
      ¬ ∃ previous ∈ frame.positionHistory, previous.board = boardSignature board := by
  simp [unseenBoards]

/-- A proof rank for complete play/pass histories, not a search cutoff. -/
def terminationRank {n : Nat} (frame : Frame n) : Nat :=
  match frame.visible.status with
  | .playing =>
      2 * (unseenBoards frame).card +
        if frame.visible.consecutivePasses = 0 then 2 else 1
  | .terminal _ => 0

theorem terminationRank_pos {n : Nat} {frame : Frame n}
    (playing : frame.visible.status = .playing) :
    0 < terminationRank frame := by
  simp only [terminationRank, playing]
  split <;> omega

theorem unseenBoards_target_subset {n : Nat} {law : Law}
    {frame target : Frame n} {move : Move n}
    (step : LegalStep law frame move target) :
    unseenBoards target ⊆ unseenBoards frame := by
  intro board unseen
  rw [mem_unseenBoards] at unseen ⊢
  intro repeated
  rcases repeated with ⟨previous, inHistory, signatureEq⟩
  apply unseen
  refine ⟨previous, ?_, signatureEq⟩
  rw [nativeStep_positionHistory_eq step]
  exact List.mem_append_left _ inHistory

theorem target_board_not_unseen {n : Nat} {law : Law}
    {frame target : Frame n} {move : Move n}
    (step : LegalStep law frame move target) :
    target.visible.board ∉ unseenBoards target := by
  rw [mem_unseenBoards]
  intro unseen
  apply unseen
  refine ⟨target.visible.situation, ?_, rfl⟩
  rw [nativeStep_positionHistory_eq step]
  simp

/-- Successful placement returns a playing child with a fresh board and a reset pass phase. -/
theorem play_step_facts {n : Nat} {komi : ℚ} {frame target : Frame n}
    {point : Point n}
    (step : LegalStep (Law.positionalSuperko komi) frame (.play point) target) :
    frame.visible.status = .playing ∧
      target.visible.status = .playing ∧
      target.visible.consecutivePasses = 0 ∧
      target.visible.board ∈ unseenBoards frame := by
  have generated := nativeStep_visible_eq step
  cases statusEq : frame.visible.status with
  | terminal reason =>
      simp [stepVisible?, playVisible?, statusEq] at generated
  | playing =>
      simp only [stepVisible?, playVisible?, statusEq] at generated
      split at generated
      · split at generated
        · split at generated
          · simp at generated
          · rename_i fresh
            simp only [Option.some.injEq] at generated
            refine ⟨rfl, ?_, ?_, ?_⟩
            · rw [← generated]
            · rw [← generated]
            · rw [mem_unseenBoards, ← generated]
              exact fresh
        · simp at generated
      · simp at generated

theorem play_unseenBoards_card_lt {n : Nat} {komi : ℚ}
    {frame target : Frame n} {point : Point n}
    (step : LegalStep (Law.positionalSuperko komi) frame (.play point) target) :
    (unseenBoards target).card < (unseenBoards frame).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨unseenBoards_target_subset step, ?_⟩
  intro equalBoards
  have fresh := (play_step_facts step).2.2.2
  rw [← equalBoards] at fresh
  exact target_board_not_unseen step fresh

theorem play_step_rank_lt {n : Nat} {komi : ℚ} {frame target : Frame n}
    {point : Point n}
    (step : LegalStep (Law.positionalSuperko komi) frame (.play point) target) :
    terminationRank target < terminationRank frame := by
  obtain ⟨sourcePlaying, targetPlaying, passesZero, _⟩ := play_step_facts step
  have cardLt := play_unseenBoards_card_lt step
  simp only [terminationRank, sourcePlaying, targetPlaying, passesZero, ite_true]
  split <;> omega

/-- Exempt pass writes the same board, flips control, and generates two-pass termination. -/
theorem pass_step_facts {n : Nat} {komi : ℚ} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko komi) frame .pass target) :
    frame.visible.status = .playing ∧
      target.visible.board = frame.visible.board ∧
      target.visible.consecutivePasses = frame.visible.consecutivePasses + 1 ∧
      target.visible.status =
        if 2 ≤ frame.visible.consecutivePasses + 1 then
          .terminal .twoPasses else .playing := by
  have generated := nativeStep_visible_eq step
  cases statusEq : frame.visible.status with
  | terminal reason =>
      simp [stepVisible?, passVisible?, statusEq] at generated
  | playing =>
      simp only [stepVisible?, passVisible?, statusEq, Law.positionalSuperko] at generated
      simp at generated
      refine ⟨rfl, ?_, ?_, ?_⟩ <;> rw [← generated]
      simp

theorem pass_step_rank_lt {n : Nat} {komi : ℚ} {frame target : Frame n}
    (step : LegalStep (Law.positionalSuperko komi) frame .pass target) :
    terminationRank target < terminationRank frame := by
  obtain ⟨sourcePlaying, _, passes, targetStatus⟩ := pass_step_facts step
  by_cases ends : 2 ≤ frame.visible.consecutivePasses + 1
  · rw [if_pos ends] at targetStatus
    simpa only [terminationRank, targetStatus] using terminationRank_pos sourcePlaying
  · have sourcePasses : frame.visible.consecutivePasses = 0 := by omega
    have targetPasses : target.visible.consecutivePasses = 1 := by omega
    rw [if_neg ends] at targetStatus
    have cardLe := Finset.card_le_card (unseenBoards_target_subset step)
    simp [terminationRank, sourcePlaying, targetStatus, sourcePasses, targetPasses]
    omega

/-- Every native non-resigning step strictly decreases the same finite rank. -/
theorem nonresigning_legalStep_rank_lt {n : Nat} {komi : ℚ}
    {frame target : Frame n} {move : Move n}
    (notResign : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko komi) frame move target) :
    terminationRank target < terminationRank frame := by
  cases move with
  | play point => exact play_step_rank_lt step
  | pass => exact pass_step_rank_lt step
  | resign => exact False.elim (notResign rfl)

/-- Reverse-oriented native play/pass edges, for recursion on legal successors. -/
def PlayPassStep {n : Nat} (komi : ℚ) (target frame : Frame n) : Prop :=
  ∃ move, move ≠ .resign ∧ LegalStep (Law.positionalSuperko komi) frame move target

/-- Original Go legality supplies the well-founded recursion relation directly. -/
theorem playPassStep_wellFounded {n : Nat} (komi : ℚ) :
    WellFounded (PlayPassStep (n := n) komi) := by
  apply Subrelation.wf (r := (measure terminationRank).rel)
  · intro target frame step
    rcases step with ⟨move, notResign, legal⟩
    exact nonresigning_legalStep_rank_lt notResign legal
  · exact (measure terminationRank).wf

end SaturationMonoid.ProcessGame.Go.CriticalKomi
