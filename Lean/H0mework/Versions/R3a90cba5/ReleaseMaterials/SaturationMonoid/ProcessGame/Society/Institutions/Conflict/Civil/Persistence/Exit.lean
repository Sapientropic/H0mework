import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Strategy
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Round

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

universe u

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community] {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "P" => Position Party Good Port Technology Instrument Observation
local notation "Strategy" => History Observation → Word

/-- Spend a fresh independent exit from this exact cut. Prior payments
remain in the whole ledger but supply no material to this new option. -/
abbrev ExitAtCut (origin : C) (command : List Party) (community : Party → Community)
    (cut : C) (exit : Word) : Prop :=
  RoundGood origin command community (Window.at cut) exit []

def HasExit (origin : C) (command : List Party) (community : Party → Community) (cut : C) : Prop :=
  ∃ exit : Word, ExitAtCut origin command community cut exit

theorem no_exit_iff_each_original_proposal_has_its_exact_issue
    (origin : C) (command : List Party) (community : Party → Community) (cut : C) :
    ¬ HasExit origin command community cut ↔ ∀ exit : Word,
      ∃ issue, inspectRound origin command community (Window.at cut) exit [] = .inl issue := by
  constructor
  · intro absent exit
    cases selected : inspectRound origin command community (Window.at cut) exit [] with
    | inl issue => exact ⟨issue, rfl⟩
    | inr checked => exact (absent ⟨exit, checked.down⟩).elim
  · rintro all ⟨exit, paid⟩
    obtain ⟨issue, _⟩ := all exit
    exact issue.refutes paid

def RequiresExit (origin : C) (command : List Party) (community : Party → Community)
    (position : P) (move reply : Word) : Prop :=
  RoundGood origin command community position.window move reply ∧
    ExitAtCut origin command community position.window.current move

def ProtectsWithExit (origin : C) (command : List Party) (community : Party → Community)
    (read : C → Observation) (strategy : Strategy) : Prop :=
  Follows origin read strategy (RequiresExit origin command community)

theorem wins_with_exit_iff_one_response_closes_each_reachable_observation_fibre
    (origin : C) (command : List Party) (community : Party → Community) (read : C → Observation) :
    (∃ strategy : Strategy, ProtectsWithExit origin command community read strategy) ↔
      ∃ family : P → Prop, family (Position.start origin read) ∧
        ClosedFor read (RequiresExit origin command community) family :=
  follows_iff_one_response_closes_each_reachable_observation_fibre origin read (RequiresExit origin command community)

/-- If the rival stops at any original input prefix, the next output of the
same observation policy is itself a fresh paid exit from that exact cut. -/
theorem every_rival_prefix_keeps_a_fresh_paid_exit_on_the_original_ledger
    {origin : C} {command : List Party} {community : Party → Community} {read : C → Observation}
    {strategy : Strategy} (wins : ProtectsWithExit origin command community read strategy)
    (rival : Nat → Word) (round : Nat) (front pending : Word) (split : rival round = front ++ pending) :
    let prior := play origin read strategy rival round
    let own := strategy prior.position.seen
    let path := prior.script ++ (own ++ front)
    let here := prior.position.extend read own front
    let exit := strategy here.seen
    (play origin read strategy rival (round + 1)).script = path ++ pending ∧
      ExitAtCut origin command community (Quantities.Execution.endAt origin path) exit ∧
      Quantities.Recorded origin (path ++ exit) ∧
      Evolving.Epoch.Current.ClosedAt (Quantities.Execution.endAt origin (path ++ exit)) := by
  let stopped (tick : Nat) := if tick = round then front else if round < tick then [] else rival tick
  have same := play_ignores_future_submissions origin read strategy rival stopped round (fun tick earlier => by
    simp [stopped, Nat.ne_of_lt earlier, Nat.not_lt_of_ge (Nat.le_of_lt earlier)])
  have atStop : stopped round = front := if_pos rfl
  have actual := wins stopped (round + 1)
  have path : (play origin read strategy stopped (round + 1)).script =
      (play origin read strategy rival round).script ++ ((strategy (play origin read strategy rival round).position.seen) ++ front) := by
    simp only [play, ← same, atStop]
  have visible : (play origin read strategy stopped (round + 1)).position =
      (play origin read strategy rival round).position.extend read (strategy (play origin read strategy rival round).position.seen) front := by
    simp only [play, ← same, atStop]
  have paid := actual.2
  change ExitAtCut origin command community (play origin read strategy stopped (round + 1)).position.window.current
    (strategy (play origin read strategy stopped (round + 1)).position.seen) at paid
  rw [play_is_the_original_execution, path, visible] at paid
  dsimp only
  refine ⟨?_, paid, Quantities.record _ _, (Quantities.record _ _).next⟩
  simp only [play, split, List.append_assoc]

/-- Inside a submitted civilian word its remaining body is already an
independent, checked continuation. The inherited partial window stays attached. -/
theorem the_rest_of_the_committed_intervention_is_an_original_checked_continuation
    {origin : C} {command : List Party} {community : Party → Community} {read : C → Observation}
    {strategy : Strategy} (wins : ProtectsWithExit origin command community read strategy)
    (rival : Nat → Word) (round : Nat) (front pending : Word)
    (split : strategy (play origin read strategy rival round).position.seen = front ++ pending) :
    let position := (play origin read strategy rival round).position
    Checked origin command community true (position.window.run front) pending ∧
      Quantities.Recorded (position.window.run front).current pending := by
  have whole := (wins rival round).1.own
  rw [split, checked_append] at whole
  exact ⟨whole.2, Quantities.record _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
