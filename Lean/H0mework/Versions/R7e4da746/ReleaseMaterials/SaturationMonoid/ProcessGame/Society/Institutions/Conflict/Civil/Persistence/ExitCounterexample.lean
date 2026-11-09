import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Exit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Finite

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

inductive FailureWithExit (origin : C) (command : List Party) (community : Party → Community)
    (position : P) (move reply : Word)
  | actual (reason : RoundFailure origin command community position.window move reply)
  | exit (reason : RoundFailure origin command community (Window.at position.window.current) move [])

theorem FailureWithExit.refutes {origin : C} {command : List Party} {community : Party → Community}
    {position : P} {move reply : Word} (issue : FailureWithExit origin command community position move reply) :
    ¬ RequiresExit origin command community position move reply := by
  intro actual
  cases issue with
  | actual reason => exact reason.refutes actual.1
  | exit reason => exact reason.refutes actual.2

def FailureWithExit.consumed {origin : C} {command : List Party} {community : Party → Community}
    {position : P} {move reply : Word} :
    FailureWithExit origin command community position move reply → Word
  | .actual issue => issue.consumed
  | .exit issue => issue.consumed

theorem FailureWithExit.consumed_is_original_prefix {origin : C} {command : List Party} {community : Party → Community}
    {position : P} {move reply : Word} (issue : FailureWithExit origin command community position move reply) :
    ∃ pending, move ++ reply = issue.consumed ++ pending := by
  cases issue with
  | actual reason => exact reason.consumed_is_original_prefix
  | exit reason =>
    obtain ⟨pending, original⟩ := reason.consumed_is_original_prefix
    refine ⟨pending ++ reply, ?_⟩
    change move ++ reply = reason.consumed ++ (pending ++ reply)
    simpa only [List.append_nil, List.append_assoc] using congrArg (fun word => word ++ reply) original

/-- Both contracts inspect the same proposed word. If both fail, retain
the one whose original input prefix reaches its obstruction first. -/
def inspectWithExit (origin : C) (command : List Party) (community : Party → Community)
    (position : P) (move reply : Word) :
    FailureWithExit origin command community position move reply ⊕
      PLift (RequiresExit origin command community position move reply) :=
  match inspectRound origin command community position.window move reply,
        inspectRound origin command community (Window.at position.window.current) move [] with
  | .inl actual, .inl exit =>
      if actual.consumed.length ≤ exit.consumed.length then .inl (.actual actual) else .inl (.exit exit)
  | .inl actual, .inr _ => .inl (.actual actual)
  | .inr _, .inl exit => .inl (.exit exit)
  | .inr actual, .inr exit => .inr ⟨⟨actual.down, exit.down⟩⟩

abbrev FirstFailureWithExit (origin : C) (command : List Party) (community : Party → Community)
    (read : C → Observation) (strategy : Strategy) (rival : List Word) :=
  FiniteFailure origin read strategy (RequiresExit origin command community)
    (FailureWithExit origin command community) rival

def inspectThroughWithExit (origin : C) (command : List Party) (community : Party → Community)
    (read : C → Observation) (strategy : Strategy) (rival : List Word) :=
  inspectFinite origin read strategy (RequiresExit origin command community)
    (FailureWithExit origin command community) (inspectWithExit origin command community) rival

def FirstFailureWithExit.originalScript {origin : C} {command : List Party} {community : Party → Community}
    {read : C → Observation} {strategy : Strategy} {rival : List Word}
    (first : FirstFailureWithExit origin command community read strategy rival) : Word :=
  (play origin read strategy (submitted rival) first.round).script ++ first.failure.consumed

theorem FirstFailureWithExit.original_prefix_and_next {origin : C} {command : List Party} {community : Party → Community}
    {read : C → Observation} {strategy : Strategy} {rival : List Word}
    (first : FirstFailureWithExit origin command community read strategy rival) :
    (∃ untouched, (play origin read strategy (submitted rival) (first.round + 1)).script =
      first.originalScript ++ untouched) ∧
    Quantities.Recorded origin first.originalScript ∧
    Evolving.Epoch.Current.ClosedAt (Quantities.Execution.endAt origin first.originalScript) := by
  obtain ⟨untouched, suffix⟩ := first.failure.consumed_is_original_prefix
  refine ⟨⟨untouched, ?_⟩, Quantities.record _ _, (Quantities.record _ _).next⟩
  simp only [play, FirstFailureWithExit.originalScript, List.append_assoc]
  exact congrArg (fun word => (play origin read strategy (submitted rival) first.round).script ++ word) suffix

theorem no_common_strategy_with_exit_iff_each_has_a_first_original_counterexample
    (origin : C) (command : List Party) (community : Party → Community) (read : C → Observation) :
    (¬ ∃ strategy : Strategy, ProtectsWithExit origin command community read strategy) ↔
      ∀ strategy : Strategy,
        Nonempty (Σ rival : List Word, FirstFailureWithExit origin command community read strategy rival) := by
  constructor
  · intro denied strategy
    exact a_failed_contract_has_an_original_first_counterexample (RequiresExit origin command community)
      (FailureWithExit origin command community) (inspectWithExit origin command community)
      (fun wins => denied ⟨strategy, wins⟩)
  · rintro counter ⟨strategy, wins⟩
    obtain ⟨rival, first⟩ := (counter strategy).some
    exact first.failure.refutes (wins (submitted rival) first.round)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
