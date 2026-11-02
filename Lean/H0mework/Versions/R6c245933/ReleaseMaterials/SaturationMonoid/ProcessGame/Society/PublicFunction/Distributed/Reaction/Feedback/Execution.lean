import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Residual
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.HistoryCoupling

/-! Compile finite optional-policy schedules into the original Machine emitter.
Each candidate executes its own words and native ledgers; omitted controls keep
the original future overrides, while explicit none suppresses only that cut. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Execution

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (source : Machine Party Good Port Technology Instrument)

abbrev Control := Option source.code.Policy

def entries (cut : Nat) : List (Control source) → List (Nat × Control source)
  | [] => []
  | control :: tail => (cut, control) :: entries (cut + 1) tail

abbrev target (cut : Nat) (term : List (Control source)) : Machine Party Good Port Technology Instrument :=
  {source with feedbackOverrides := source.feedbackOverrides ++ entries source cut term}

/-- The baseline is the original machine, including its actual root emitter. -/
theorem empty_schedule_is_the_original_source (cut : Nat) : target source cut [] = source := by
  cases source
  simp [target, entries]

private theorem fold_before (cut index : Nat) (earlier : index < cut)
    (term : List (Control source)) (prior : Control source) :
    (entries source cut term).foldl (fun prior entry => if entry.1 = index then entry.2 else prior) prior = prior := by
  induction term generalizing cut prior with
  | nil => rfl
  | cons control tail ih =>
    simp only [entries, List.foldl_cons, if_neg (show cut ≠ index by omega)]
    exact ih (cut + 1) (by omega) prior

private theorem fold_at (cut offset : Nat) (term : List (Control source)) (prior : Control source) :
    (entries source cut term).foldl (fun prior entry => if entry.1 = cut + offset then entry.2 else prior) prior =
      (term[offset]?).getD prior := by
  induction term generalizing cut offset prior with
  | nil => rfl
  | cons control tail ih =>
    cases offset with
    | zero =>
      simp only [Nat.add_zero, entries, List.foldl_cons, List.getElem?_cons_zero, Option.getD_some]
      exact fold_before source (cut + 1) cut (by omega) tail control
    | succ offset =>
      simp only [entries, List.foldl_cons, if_neg (show cut ≠ cut + (offset + 1) by omega), List.getElem?_cons_succ]
      rw [show cut + (offset + 1) = cut + 1 + offset by omega]
      exact ih (cut + 1) offset prior

theorem policy_before (cut : Nat) (term : List (Control source)) (index : Nat) (earlier : index < cut) :
    (target source cut term).feedbackPolicy index = source.feedbackPolicy index := by
  unfold Machine.feedbackPolicy
  rw [List.foldl_append]
  exact fold_before source cut index earlier term _

theorem policy_at (cut : Nat) (term : List (Control source)) (offset : Nat) :
    (target source cut term).feedbackPolicy (cut + offset) = Residual.scheduleAt source cut term offset := by
  unfold Machine.feedbackPolicy
  rw [List.foldl_append]
  exact fold_at source cut offset term _

variable (input : Input source.code) (cut : Nat) (term : List (Control source))

theorem complete_state_before (count : Nat) (bounded : count ≤ cut) :
    (target source cut term).feedbackState input count = source.feedbackState input count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Machine.feedbackState, policy_before source cut term count (by omega), ih (by omega)]
    rfl

/-- The schedule interpreter and its own emitter produce the same complete state. -/
theorem the_whole_scheduled_run_is_the_actual_state (n : Nat) :
    (target source cut term).feedbackState input (cut + n) =
      Residual.run source.code (Residual.scheduleAt source cut term) input (Residual.seed source input cut) n := by
  induction n with
  | zero => exact complete_state_before source input cut term cut (Nat.le_refl _)
  | succ n ih =>
    rw [show cut + (n + 1) = (cut + n) + 1 by omega, Machine.feedbackState, policy_at, ih]
    rfl

theorem earlier_body (current : RawCurrent Party Good Technology Instrument)
    (bounded : current.round - source.code.initial.round - 1 < source.history.length + 1 + cut) :
    (target source cut term).body current = source.body current := by
  unfold Machine.body
  dsimp only [target]
  split
  · rfl
  · split
    · split
      · rfl
      · unfold Machine.laterResponse
        dsimp only [target]
        split
        · rfl
        next actual active =>
          rw [policy_before source cut term _ (by omega), complete_state_before source actual cut term _ (by omega)]
    · rfl

theorem prior_raw_event (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) :
    ProgrammeSource.rawEvent (target source cut term).input (ProgrammeHistory.visitAt source.input ordinal).current =
      ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt source.input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (target source cut term).body current = source.body current
    apply earlier_body source cut term current
    have rounds := ProgrammeHistory.visit_round source.input ordinal
    rw [view] at rounds
    change current.round = source.code.initial.round + ordinal at rounds
    omega

variable (active : source.feedback? = some input) (empty : source.continuation = [])

include active empty in
theorem scheduled_current_is_the_actual_source_current (n : Nat) :
    (target source cut term).currentAt (source.history.length + 2 + (cut + n)) =
      (Residual.run source.code (Residual.scheduleAt source cut term) input (Residual.seed source input cut) n).current := by
  exact ((target source cut term).feedback_current_is_actual input active empty (cut + n)).trans
    (congrArg State.current (the_whole_scheduled_run_is_the_actual_state source input cut term n))

include active empty in
theorem scheduled_word_is_actually_submitted (n : Nat) :
    ((target source cut term).actualExecution (source.history.length + 1 + (cut + n))).submitted =
      word source.code (Residual.scheduleAt source cut term n) input
        (Residual.run source.code (Residual.scheduleAt source cut term) input (Residual.seed source input cut) n) := by
  rw [(target source cut term).feedback_word_is_actual input active empty,
    policy_at, the_whole_scheduled_run_is_the_actual_state]

/-- Preserve every original account before the first scheduled control. -/
theorem complete_finance_before (ordinal : Nat) (bounded : ordinal ≤ source.history.length + 2 + cut) :
    Native.Coupling.Match source.code source.input (target source cut term).input
      (Financial.accountAt source.input ordinal) (Financial.accountAt (target source cut term).input ordinal) :=
  Native.Coupling.History.complete_accounts source.code source.input (target source cut term).input rfl rfl
    (source.history.length + 2 + cut) (prior_raw_event source cut term)
    source.body (target source cut term).body rfl rfl ordinal bounded

/-- Actual emitted words, full prefix transport and the candidate's own native runs. -/
structure Disposition where
  finance_prefix : ∀ ordinal, ordinal ≤ source.history.length + 2 + cut →
    Native.Coupling.Match source.code source.input (target source cut term).input
      (Financial.accountAt source.input ordinal) (Financial.accountAt (target source cut term).input ordinal)
  prior_state : (target source cut term).feedbackState input cut = source.feedbackState input cut
  complete_states : ∀ n, (target source cut term).feedbackState input (cut + n) =
    Residual.run source.code (Residual.scheduleAt source cut term) input (Residual.seed source input cut) n
  actual_words : ∀ n, ((target source cut term).actualExecution (source.history.length + 1 + (cut + n))).submitted =
    word source.code (Residual.scheduleAt source cut term n) input
      (Residual.run source.code (Residual.scheduleAt source cut term) input (Residual.seed source input cut) n)
  native : (n : Nat) → Native.Disposition (target source cut term) (source.history.length + 1 + (cut + n))
  native_exact : native = fun n => Native.generate (target source cut term) (source.history.length + 1 + (cut + n))

include active empty in
def generate : Disposition source input cut term where
  finance_prefix := complete_finance_before source cut term
  prior_state := complete_state_before source input cut term cut (Nat.le_refl _)
  complete_states := the_whole_scheduled_run_is_the_actual_state source input cut term
  actual_words := scheduled_word_is_actually_submitted source input cut term active empty
  native := fun n => Native.generate (target source cut term) (source.history.length + 1 + (cut + n))
  native_exact := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Execution
