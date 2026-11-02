import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Update

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

abbrev Schedule := Nat → Option code.Policy

def run (schedule : Schedule code) (input : Input code) (seed : State code) : Nat → State code
  | 0 => seed
  | n + 1 => advance code (schedule n) input (run schedule input seed n)

def forced (policy : Option code.Policy) (move : Move code) (state : State code) : State code :=
  advance code policy ⟨fun _ _ _ => move, 0⟩ state

omit [DecidableEq Port] [DecidableEq Technology] in
theorem advance_is_its_actual_choice (policy : Option code.Policy) (input : Input code) (state : State code) :
    advance code policy input state = forced code policy
      (input.opponent state.history state.past state.frame) state := rfl

def replay (schedule : Schedule code) : Nat → State code → List (Move code) → State code
  | _, seed, [] => seed
  | offset, seed, move :: tail => replay schedule (offset + 1) (forced code (schedule offset) move seed) tail

omit [DecidableEq Port] [DecidableEq Technology] in
theorem replay_append_one (schedule : Schedule code) (offset : Nat) (seed : State code)
    (priorMoves : List (Move code)) (move : Move code) :
    replay code schedule offset seed (priorMoves ++ [move]) =
      forced code (schedule (offset + priorMoves.length)) move (replay code schedule offset seed priorMoves) := by
  induction priorMoves generalizing offset seed with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons_append, replay, ih, List.length_cons]
    congr 2
    omega

def responses (schedule : Schedule code) (input : Input code) (seed : State code) : Nat → List (Move code)
  | 0 => []
  | n + 1 => responses schedule input seed n ++
      [input.opponent (run code schedule input seed n).history
        (run code schedule input seed n).past (run code schedule input seed n).frame]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem responses_length (schedule : Schedule code) (input : Input code) (seed : State code) (n : Nat) :
    (responses code schedule input seed n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [responses, List.length_append, List.length_singleton, ih]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem responses_supported (schedule : Schedule code) (input : Input code) (seed : State code) (n : Nat) :
    ∀ move ∈ responses code schedule input seed n, move ∈ moves code := by
  intro move _
  exact every_move_is_generated code move

omit [DecidableEq Port] [DecidableEq Technology] in
theorem replay_responses_is_the_whole_run (schedule : Schedule code) (input : Input code)
    (seed : State code) (n : Nat) :
    replay code schedule 0 seed (responses code schedule input seed n) = run code schedule input seed n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [responses, replay_append_one, ih, responses_length]
    simpa only [Nat.zero_add, run] using
      (advance_is_its_actual_choice code (schedule n) input (run code schedule input seed n)).symm

omit [DecidableEq Port] [DecidableEq Technology] in
theorem remaining_is_the_seed_budget (schedule : Schedule code) (input : Input code) (seed : State code) (n : Nat) :
    (run code schedule input seed n).remaining = seed.remaining - n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, advance, ih, Nat.sub_sub]

def key (state : State code) : Key code := (state.history, state.past, state.frame)

variable (seed : State code) (programs : List (Schedule code))

def keys : List (Key code) :=
  (programs.flatMap fun schedule =>
    ((sequences (moves code) seed.remaining).filter (fun responses => responses.length < seed.remaining)).map
      (fun responses => key code (replay code schedule 0 seed responses))).dedup

theorem every_remaining_decision_is_generated (schedule : Schedule code) (generated : schedule ∈ programs)
    (input : Input code) (n : Nat) (bounded : n < seed.remaining) :
    key code (run code schedule input seed n) ∈ keys code seed programs := by
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨schedule, generated, List.mem_map.mpr ?_⟩
  refine ⟨responses code schedule input seed n, List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (mem_sequences_iff _ _ _).mpr ⟨by rw [responses_length]; omega,
      responses_supported code schedule input seed n⟩
  · simpa only [responses_length, decide_eq_true_eq] using bounded
  · exact congrArg (key code) (replay_responses_is_the_whole_run code schedule input seed n)

theorem exhausted_seed_has_no_decision_keys (stopped : seed.remaining = 0) :
    keys code seed programs = [] := by
  simp [keys, stopped, sequences]

abbrev Table := ∀ key ∈ keys code seed programs, Move code

def tables : List (Table code seed programs) := List.pi (keys code seed programs) (fun _ => moves code)

def respond (table : Table code seed programs) : Opponent code := fun history past frame =>
  if member : (history, past, frame) ∈ keys code seed programs then table _ member else none

def restrict (opponent : Opponent code) : Table code seed programs := fun key _ => opponent key.1 key.2.1 key.2.2

theorem restriction_is_generated (opponent : Opponent code) :
    restrict code seed programs opponent ∈ tables code seed programs := by
  apply (List.mem_pi _ _).mpr
  intro _ _
  exact every_move_is_generated code _

theorem restriction_agrees (opponent : Opponent code) (state : State code)
    (inside : key code state ∈ keys code seed programs) :
    respond code seed programs (restrict code seed programs opponent) state.history state.past state.frame =
      opponent state.history state.past state.frame := by
  dsimp only [key] at inside
  simp only [respond, dif_pos inside, restrict]

theorem one_restriction_preserves_the_whole_remaining_run
    (schedule : Schedule code) (generated : schedule ∈ programs) (input : Input code)
    (n : Nat) (bounded : n ≤ seed.remaining) :
    run code schedule ⟨respond code seed programs (restrict code seed programs input.opponent), input.budget⟩ seed n =
      run code schedule input seed n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    rw [ih (by omega), advance_is_its_actual_choice, advance_is_its_actual_choice code (schedule n) input]
    exact congrArg (fun move => forced code (schedule n) move (run code schedule input seed n))
      (restriction_agrees code seed programs input.opponent _
        (every_remaining_decision_is_generated code seed programs schedule generated input n (by omega)))

theorem every_opponent_has_one_joint_remaining_table (input : Input code) :
    ∃ table ∈ tables code seed programs, ∀ schedule ∈ programs, ∀ n ≤ seed.remaining,
      run code schedule ⟨respond code seed programs table, input.budget⟩ seed n =
        run code schedule input seed n := by
  exact ⟨restrict code seed programs input.opponent, restriction_is_generated code seed programs input.opponent,
    fun schedule generated n bounded => one_restriction_preserves_the_whole_remaining_run code seed programs schedule generated input n bounded⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)

abbrev seed := source.feedbackState input cut

def controlMenu : List (Option source.code.Policy) :=
  none :: source.policy? :: source.feedbackOverrides.map Prod.snd ++ source.code.policies.map some

def scheduleTerms := sequences (controlMenu source) (seed source input cut).remaining

/-- An omitted suffix keeps the source's actual future overrides. Explicit none
is a policy choice and does not discard subsequent cuts. -/
def scheduleAt (term : List (Option source.code.Policy)) : Schedule source.code := fun offset =>
  (term[offset]?).getD (source.feedbackPolicy (cut + offset))

def schedules : List (Schedule source.code) := (scheduleTerms source input cut).map (scheduleAt source cut)

theorem every_supported_schedule_is_generated (term : List (Option source.code.Policy))
    (bounded : term.length ≤ (seed source input cut).remaining)
    (supported : ∀ control ∈ term, control ∈ controlMenu source) :
    scheduleAt source cut term ∈ schedules source input cut :=
  List.mem_map.mpr ⟨term, (mem_sequences_iff _ _ _).mpr ⟨bounded, supported⟩, rfl⟩

theorem the_actual_baseline_schedule_is_generated : scheduleAt source cut [] ∈ schedules source input cut :=
  every_supported_schedule_is_generated source input cut [] (Nat.zero_le _) (by simp)

theorem baseline_is_the_complete_actual_successor (n : Nat) :
    run source.code (scheduleAt source cut []) input (seed source input cut) n =
      source.feedbackState input (cut + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, ih]
    rfl

theorem all_candidates_share_one_remaining_opponent_table :
    ∃ table ∈ tables source.code (seed source input cut) (schedules source input cut),
      ∀ schedule ∈ schedules source input cut, ∀ n ≤ (seed source input cut).remaining,
        run source.code schedule
          ⟨respond source.code (seed source input cut) (schedules source input cut) table, input.budget⟩
          (seed source input cut) n = run source.code schedule input (seed source input cut) n :=
  every_opponent_has_one_joint_remaining_table source.code (seed source input cut) (schedules source input cut) input


def FutureCoverage : Prop :=
  ∀ opponent : Opponent source.code,
    ∃ table ∈ tables source.code (seed source input cut) (schedules source input cut),
      ∀ schedule ∈ schedules source input cut, ∀ n ≤ (seed source input cut).remaining,
        run source.code schedule
          ⟨respond source.code (seed source input cut) (schedules source input cut) table, input.budget⟩
          (seed source input cut) n =
        run source.code schedule ⟨opponent, input.budget⟩ (seed source input cut) n

theorem every_future_opponent_is_jointly_covered : FutureCoverage source input cut :=
  fun opponent => every_opponent_has_one_joint_remaining_table source.code (seed source input cut)
    (schedules source input cut) ⟨opponent, input.budget⟩

structure Disposition where
  future_coverage : FutureCoverage source input cut
  table : Table source.code (seed source input cut) (schedules source input cut)
  generated : table ∈ tables source.code (seed source input cut) (schedules source input cut)
  whole_runs : ∀ schedule ∈ schedules source input cut, ∀ n ≤ (seed source input cut).remaining,
    run source.code schedule
        ⟨respond source.code (seed source input cut) (schedules source input cut) table, input.budget⟩
        (seed source input cut) n = run source.code schedule input (seed source input cut) n
  baseline_actual : ∀ n ≤ (seed source input cut).remaining,
    run source.code (scheduleAt source cut [])
        ⟨respond source.code (seed source input cut) (schedules source input cut) table, input.budget⟩
        (seed source input cut) n = source.feedbackState input (cut + n)

def generate : Disposition source input cut where
  future_coverage := every_future_opponent_is_jointly_covered source input cut
  table := restrict source.code (seed source input cut) (schedules source input cut) input.opponent
  generated := restriction_is_generated source.code (seed source input cut) (schedules source input cut) input.opponent
  whole_runs := fun schedule generated n bounded =>
    one_restriction_preserves_the_whole_remaining_run source.code (seed source input cut)
      (schedules source input cut) schedule generated input n bounded
  baseline_actual := fun n bounded =>
    (one_restriction_preserves_the_whole_remaining_run source.code (seed source input cut)
      (schedules source input cut) _ (the_actual_baseline_schedule_is_generated source input cut) input n bounded).trans
      (baseline_is_the_complete_actual_successor source input cut n)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual
