import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Termination
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.ScoreReadout

/-!
# Executable continuation of a Go survival invariant

A policy reads the current native frame, including its already-written superko
history, and generates one legal play/pass successor.  Strict native progress
compiles any two policies into an actual two-pass terminal replay without fuel.
The invariant closure below is a conditional consumer: its own-move generator,
universal opponent preservation and terminal readout remain explicit inputs.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

/-- One executable native play/pass occurrence at the supplied history. -/
structure ScoringReply {n : Nat} (frame : Frame n) where
  move : Move n
  target : Frame n
  notResign : move ≠ .resign
  step : LegalStep (Law.positionalSuperko 0) frame move target

/-- A history-dependent response generator.  There is no future opponent input. -/
structure ExecutablePolicy (n : Nat) where
  reply : (frame : Frame n) → frame.visible.status = .playing → ScoringReply frame

/-- Exempt pass is a native legal fallback at every playing frame. -/
def passReply {n : Nat} (frame : Frame n)
    (playing : frame.visible.status = .playing) : ScoringReply frame where
  move := .pass
  target := frame.advance {
    board := frame.visible.board
    toMove := frame.visible.toMove.other
    consecutivePasses := frame.visible.consecutivePasses + 1
    status := if 2 ≤ frame.visible.consecutivePasses + 1 then
      .terminal .twoPasses else .playing
  }
  notResign := by intro same; cases same
  step := by
    simp [LegalStep, nativeStep?, stepVisible?, passVisible?, playing, Law.positionalSuperko]

def passPolicy (n : Nat) : ExecutablePolicy n where
  reply := passReply

/-- Histories relevant to area scoring exclude resignation terminals. -/
def ScoringStatus {n : Nat} (frame : Frame n) : Prop :=
  frame.visible.status = .playing ∨ frame.visible.status = .terminal .twoPasses

theorem nonresigning_step_playing {n : Nat} {frame target : Frame n} {move : Move n}
    (notResign : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    frame.visible.status = .playing := by
  cases move with
  | play point => exact (play_step_facts step).1
  | pass => exact (pass_step_facts step).1
  | resign => exact False.elim (notResign rfl)

theorem nonresigning_step_scoringStatus {n : Nat} {frame target : Frame n}
    {move : Move n} (notResign : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    ScoringStatus target := by
  cases move with
  | play point => exact Or.inl (play_step_facts step).2.1
  | pass =>
      have status := (pass_step_facts step).2.2.2
      split at status
      · exact Or.inr status
      · exact Or.inl status
  | resign => exact False.elim (notResign rfl)

/-- The beneficiary's moves follow this policy; all opponent play/pass deviations remain free. -/
def FollowsPolicy {n : Nat} (beneficiary : Polarity) (policy : ExecutablePolicy n) :
    {start : Frame n} → {moves : List (Move n)} →
      GeneratedReplay (Law.positionalSuperko 0) start moves → Prop
  | _, _, .nil _ => True
  | start, _, .cons move _ tail =>
      move ≠ .resign ∧
        (start.visible.toMove = beneficiary →
          ∀ playing : start.visible.status = .playing,
            move = (policy.reply start playing).move) ∧
        FollowsPolicy beneficiary policy tail

/-- Actual full execution, including the exact move word and terminal cause. -/
structure CompletedPlay {n : Nat} (profile : Polarity → ExecutablePolicy n)
    (start : Frame n) where
  moves : List (Move n)
  replay : GeneratedReplay (Law.positionalSuperko 0) start moves
  terminal : replay.final.visible.status = .terminal .twoPasses
  follows : ∀ beneficiary, FollowsPolicy beneficiary (profile beneficiary) replay

/-- Execute only generated native successors until the original two-pass terminal. -/
def executePolicies {n : Nat} (profile : Polarity → ExecutablePolicy n)
    (start : Frame n) (scoring : ScoringStatus start) : CompletedPlay profile start :=
  match statusEq : start.visible.status with
  | .playing =>
      let reply := (profile start.visible.toMove).reply start statusEq
      let rest := executePolicies profile reply.target
        (nonresigning_step_scoringStatus reply.notResign reply.step)
      {
        moves := reply.move :: rest.moves
        replay := .cons reply.move reply.step rest.replay
        terminal := rest.terminal
        follows := by
          intro beneficiary
          refine ⟨reply.notResign, ?_, rest.follows beneficiary⟩
          intro owned playing
          dsimp [reply]
          subst beneficiary
          rfl
      }
  | .terminal reason =>
      have scored : reason = .twoPasses := by
        rcases scoring with playing | scored
        · rw [statusEq] at playing
          contradiction
        · rw [statusEq] at scored
          exact Status.terminal.inj scored
      {
        moves := []
        replay := .nil start
        terminal := by simpa only [GeneratedReplay.final, scored] using statusEq
        follows := by intro beneficiary; trivial
      }
termination_by terminationRank start
decreasing_by exact nonresigning_legalStep_rank_lt reply.notResign reply.step

/-- Every pair of executable policies yields an actual scored game from the empty board. -/
def initialPlay (n : Nat) (profile : Polarity → ExecutablePolicy n) :
    CompletedPlay profile (Frame.initial n) :=
  executePolicies profile (Frame.initial n) (Or.inl rfl)

/-- A source-indexed invariant contract with one generated own move and all legal opponent moves. -/
structure SurvivalClosure {n : Nat} (beneficiary : Polarity)
    (Invariant Good : Frame n → Prop) where
  ownReply : (frame : Frame n) → Invariant frame → frame.visible.toMove = beneficiary →
    frame.visible.status = .playing → ScoringReply frame
  own_preserved : ∀ frame inside owned playing,
    Invariant (ownReply frame inside owned playing).target
  opponent_preserved : ∀ {frame target : Frame n} {move : Move n},
    Invariant frame → frame.visible.toMove ≠ beneficiary → move ≠ .resign →
      LegalStep (Law.positionalSuperko 0) frame move target → Invariant target
  finished : ∀ {frame : Frame n}, Invariant frame →
    frame.visible.status = .terminal .twoPasses → Good frame

namespace SurvivalClosure

/-- Compile the local closure generator into a total history policy, with legal pass outside it. -/
def policy {n : Nat} {beneficiary : Polarity} {Invariant Good : Frame n → Prop}
    [DecidablePred Invariant] (closure : SurvivalClosure beneficiary Invariant Good) :
    ExecutablePolicy n where
  reply frame playing :=
    if inside : Invariant frame then
      if owned : frame.visible.toMove = beneficiary then
        closure.ownReply frame inside owned playing
      else passReply frame playing
    else passReply frame playing

theorem policy_reply_inside {n : Nat} {beneficiary : Polarity}
    {Invariant Good : Frame n → Prop} [DecidablePred Invariant]
    (closure : SurvivalClosure beneficiary Invariant Good) (frame : Frame n)
    (inside : Invariant frame) (owned : frame.visible.toMove = beneficiary)
    (playing : frame.visible.status = .playing) :
    closure.policy.reply frame playing = closure.ownReply frame inside owned playing := by
  simp [policy, inside, owned]

/-- The invariant propagates through every opponent deviation and every selected own move. -/
theorem preserves_replay {n : Nat} {beneficiary : Polarity}
    {Invariant Good : Frame n → Prop} [DecidablePred Invariant]
    (closure : SurvivalClosure beneficiary Invariant Good)
    {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay (Law.positionalSuperko 0) start moves)
    (inside : Invariant start)
    (follows : FollowsPolicy beneficiary closure.policy replay) :
    Invariant replay.final := by
  induction replay with
  | nil => exact inside
  | @cons frame target moves move step tail ih =>
      rcases follows with ⟨notResign, followsOwn, followsTail⟩
      apply ih _ followsTail
      by_cases owned : frame.visible.toMove = beneficiary
      · have playing := nonresigning_step_playing notResign step
        have moveEq := followsOwn owned playing
        rw [closure.policy_reply_inside frame inside owned playing] at moveEq
        have sameTarget : target = (closure.ownReply frame inside owned playing).target := by
          apply legalStep_target_unique step
          rw [moveEq]
          exact (closure.ownReply frame inside owned playing).step
        rw [sameTarget]
        exact closure.own_preserved frame inside owned playing
      · exact closure.opponent_preserved inside owned notResign step

/-- Any actual two-pass terminal reached while following this policy satisfies the terminal goal. -/
theorem terminal_good {n : Nat} {beneficiary : Polarity}
    {Invariant Good : Frame n → Prop} [DecidablePred Invariant]
    (closure : SurvivalClosure beneficiary Invariant Good)
    {start : Frame n} {moves : List (Move n)}
    (replay : GeneratedReplay (Law.positionalSuperko 0) start moves)
    (inside : Invariant start)
    (follows : FollowsPolicy beneficiary closure.policy replay)
    (terminal : replay.final.visible.status = .terminal .twoPasses) :
    Good replay.final :=
  closure.finished (closure.preserves_replay replay inside follows) terminal

end SurvivalClosure

/-- Use the given policy on its own control polarity and an arbitrary opponent policy otherwise. -/
def versus {n : Nat} (beneficiary : Polarity)
    (policy opponent : ExecutablePolicy n) : Polarity → ExecutablePolicy n :=
  fun colour => if colour = beneficiary then policy else opponent

@[simp] theorem versus_self {n : Nat} (beneficiary : Polarity)
    (policy opponent : ExecutablePolicy n) :
    versus beneficiary policy opponent beneficiary = policy := by
  simp [versus]

/-- The closure contract yields both a complete actual play and its goal against every policy. -/
theorem SurvivalClosure.against_every_policy {n : Nat} {beneficiary : Polarity}
    {Invariant Good : Frame n → Prop} [DecidablePred Invariant]
    (closure : SurvivalClosure beneficiary Invariant Good)
    {start : Frame n} (inside : Invariant start) (scoring : ScoringStatus start)
    (opponent : ExecutablePolicy n) :
    Good (executePolicies (versus beneficiary closure.policy opponent) start scoring).replay.final := by
  let played := executePolicies (versus beneficiary closure.policy opponent) start scoring
  apply closure.terminal_good played.replay inside _ played.terminal
  simpa using played.follows beneficiary

/-- Both unilateral guarantees hold at the same actual profile, so its integral margin is exact. -/
theorem dual_closures_exact_margin {n : Nat} {whiteInvariant blackInvariant : Frame n → Prop}
    [DecidablePred whiteInvariant] [DecidablePred blackInvariant]
    (c : Int)
    (white : SurvivalClosure .negative whiteInvariant (fun frame =>
      (areaScore frame.visible.board .positive : Int) -
        (areaScore frame.visible.board .negative : Int) ≤ c))
    (black : SurvivalClosure .positive blackInvariant (fun frame =>
      c ≤ (areaScore frame.visible.board .positive : Int) -
        (areaScore frame.visible.board .negative : Int)))
    (whiteInitial : whiteInvariant (Frame.initial n))
    (blackInitial : blackInvariant (Frame.initial n)) :
    let played := initialPlay n (versus .negative white.policy black.policy)
    (areaScore played.replay.final.visible.board .positive : Int) -
      (areaScore played.replay.final.visible.board .negative : Int) = c := by
  intro played
  have whiteFollows : FollowsPolicy .negative white.policy played.replay := by
    simpa using played.follows .negative
  have blackFollows : FollowsPolicy .positive black.policy played.replay := by
    simpa [versus] using played.follows .positive
  have upper := white.terminal_good played.replay whiteInitial whiteFollows played.terminal
  have lower := black.terminal_good played.replay blackInitial blackFollows played.terminal
  exact Int.le_antisymm upper lower

end SaturationMonoid.ProcessGame.Go.CriticalKomi
