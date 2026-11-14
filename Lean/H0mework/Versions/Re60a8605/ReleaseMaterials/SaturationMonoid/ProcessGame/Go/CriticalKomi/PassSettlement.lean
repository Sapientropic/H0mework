import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Forcing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Survival

/-!
A native family of closed score obligations.  Once the preceding actual move
was pass, the mover can settle the current area margin immediately.  This
generates a unilateral bound for all thresholds from one unchanged-board law.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

def PassRegion {n : Nat} (beneficiary : Polarity) (good : Board n → Prop)
    (frame : Frame n) : Prop :=
  good frame.visible.board ∧
    (frame.visible.status = .terminal .twoPasses ∨
      (frame.visible.toMove = beneficiary ∧ 1 ≤ frame.visible.consecutivePasses))

instance {n : Nat} (beneficiary : Polarity) (good : Board n → Prop) [DecidablePred good] :
    DecidablePred (PassRegion beneficiary good) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The source's same-board pass equation generates this whole terminal-response family. -/
def passSurvival {n : Nat} (beneficiary : Polarity) (good : Board n → Prop) :
    SurvivalClosure beneficiary (PassRegion beneficiary good)
      (fun frame => good frame.visible.board) where
  ownReply frame _ _ playing := passReply frame playing
  own_preserved frame inside _ playing := by
    have passes : 1 ≤ frame.visible.consecutivePasses := by
      rcases inside.2 with terminal | ready
      · rw [playing] at terminal
        contradiction
      · exact ready.2
    have ends : 2 ≤ frame.visible.consecutivePasses + 1 := by omega
    exact ⟨inside.1, Or.inl (by simp [passReply, Frame.advance, ends])⟩
  opponent_preserved := by
    intro frame target move inside opponent _ step
    rcases inside.2 with terminal | ready
    · have impossible := nativeStep_eq_none_of_terminal (Law.positionalSuperko 0)
        frame .twoPasses terminal move
      rw [step] at impossible
      contradiction
    · exact False.elim (opponent ready.1)
  finished inside _ := inside.1

theorem passSurvival_policy {n : Nat} (beneficiary : Polarity) (good : Board n → Prop)
    [DecidablePred good] : (passSurvival beneficiary good).policy = passPolicy n := by
  unfold SurvivalClosure.policy passPolicy
  congr 1
  funext frame playing
  simp only [passSurvival]
  split <;> simp

/-- White's actual pass opportunity produces an upper bound equal to the current area score. -/
theorem white_pass_bound {n : Nat} (frame : Frame n)
    (owned : frame.visible.toMove = .negative) (passed : 1 ≤ frame.visible.consecutivePasses)
    (playing : frame.visible.status = .playing) (opponent : ExecutablePolicy n) :
    let closure := passSurvival .negative
      (fun board : Board n => areaMargin board ≤ areaMargin frame.visible.board)
    areaMargin (executePolicies (versus .negative closure.policy opponent) frame
      (Or.inl playing)).replay.final.visible.board ≤ areaMargin frame.visible.board := by
  exact (passSurvival .negative
    (fun board : Board n => areaMargin board ≤ areaMargin frame.visible.board)).against_every_policy
    ⟨Int.le_refl _, Or.inr ⟨owned, passed⟩⟩ (Or.inl playing) opponent

/-- Black's actual pass opportunity produces the corresponding lower bound. -/
theorem black_pass_bound {n : Nat} (frame : Frame n)
    (owned : frame.visible.toMove = .positive) (passed : 1 ≤ frame.visible.consecutivePasses)
    (playing : frame.visible.status = .playing) (opponent : ExecutablePolicy n) :
    let closure := passSurvival .positive
      (fun board : Board n => areaMargin frame.visible.board ≤ areaMargin board)
    areaMargin frame.visible.board ≤
      areaMargin (executePolicies (versus .positive closure.policy opponent) frame
        (Or.inl playing)).replay.final.visible.board := by
  exact (passSurvival .positive
    (fun board : Board n => areaMargin frame.visible.board ≤ areaMargin board)).against_every_policy
    ⟨Int.le_refl _, Or.inr ⟨owned, passed⟩⟩ (Or.inl playing) opponent

def afterOpeningPass19 : Frame 19 := (passReply (Frame.initial 19) rfl).target

theorem areaMargin_empty (n : Nat) : areaMargin (Board.empty : Board n) = 0 := by
  have territory (point : Point n) : territoryOwner? (Board.empty : Board n) point = none := by
    simp [territoryOwner?, borderingColours, Board.empty]
  simp [areaMargin, areaScore, Board.empty, territory]

/-- A real first-ply obligation of the 19x19 root, with a complete unilateral policy. -/
theorem opening_pass_white_bound (opponent : ExecutablePolicy 19) :
    areaMargin (executePolicies (versus .negative (passPolicy 19) opponent)
      afterOpeningPass19 (Or.inl rfl)).replay.final.visible.board ≤ 0 := by
  have bound := white_pass_bound afterOpeningPass19 rfl (by decide) rfl opponent
  dsimp only at bound
  rw [passSurvival_policy] at bound
  have sourceScore : areaMargin afterOpeningPass19.visible.board = 0 := areaMargin_empty 19
  exact bound.trans_eq sourceScore

end SaturationMonoid.ProcessGame.Go.CriticalKomi
