import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Execution

/-! Future decisions use only visible history; the original emitter retains its past. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument) (input : Input source.code) (cut : Nat)
  (opponent : Opponent source.code)

abbrev takeover : Input source.code :=
  ⟨fun history past frame =>
    if history.length < source.history.length + 1 + cut then input.opponent history past frame
    else opponent history past frame, input.budget⟩

abbrev target (term : List (Option source.code.Policy)) : Machine Party Good Port Technology Instrument :=
  Execution.target {source with feedback? := some (takeover source input cut opponent)} cut term

theorem original_response_is_preserved (term : List (Option source.code.Policy)) :
    (target source input cut opponent term).responseFrame = source.responseFrame := rfl

private theorem history_length (count : Nat) :
    (source.feedbackState input count).history.length = source.history.length + 1 + count := by
  induction count with
  | zero => simp [Machine.feedbackState, Machine.feedbackInitial]
  | succ count ih =>
    change (advance source.code _ input _).history.length = _
    rw [history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
    omega

private theorem word_before (policy : Option source.code.Policy) (state : State source.code)
    (earlier : state.history.length < source.history.length + 1 + cut) :
    word source.code policy (takeover source input cut opponent) state = word source.code policy input state := by
  simp only [word, decision, if_pos earlier]

private theorem advance_before (policy : Option source.code.Policy) (state : State source.code)
    (earlier : state.history.length < source.history.length + 1 + cut) :
    advance source.code policy (takeover source input cut opponent) state = advance source.code policy input state := by
  simp only [advance, word, decision, if_pos earlier]

private theorem advance_after (policy : Option source.code.Policy) (state : State source.code)
    (later : source.history.length + 1 + cut ≤ state.history.length) :
    advance source.code policy (takeover source input cut opponent) state =
      advance source.code policy ⟨opponent, input.budget⟩ state := by
  simp only [advance, word, decision, if_neg (show ¬state.history.length < source.history.length + 1 + cut by omega)]

variable (term : List (Option source.code.Policy))

private theorem policy_before (index : Nat) (earlier : index < cut) :
    (target source input cut opponent term).feedbackPolicy index = source.feedbackPolicy index :=
  Execution.policy_before {source with feedback? := some (takeover source input cut opponent)} cut term index earlier

private theorem policy_at (offset : Nat) :
    (target source input cut opponent term).feedbackPolicy (cut + offset) = Residual.scheduleAt source cut term offset :=
  Execution.policy_at {source with feedback? := some (takeover source input cut opponent)} cut term offset

theorem complete_state_before (count : Nat) (bounded : count ≤ cut) :
    (target source input cut opponent term).feedbackState (takeover source input cut opponent) count =
      source.feedbackState input count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [Machine.feedbackState, policy_before source input cut opponent term count (by omega), ih (by omega)]
    exact advance_before source input cut opponent _ _ (by rw [history_length]; omega)

private theorem run_history_length (n : Nat) :
    (Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩
      (Residual.seed source input cut) n).history.length = source.history.length + 1 + cut + n := by
  induction n with
  | zero => exact history_length source input cut
  | succ n ih =>
    change (advance source.code _ _ _).history.length = _
    rw [history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
    omega

/-- Memory, mailboxes and unspent budget are the original actual seed. -/
theorem the_whole_future_run_is_the_actual_state (n : Nat) :
    (target source input cut opponent term).feedbackState (takeover source input cut opponent) (cut + n) =
      Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩
        (Residual.seed source input cut) n := by
  induction n with
  | zero => exact complete_state_before source input cut opponent term cut (Nat.le_refl _)
  | succ n ih =>
    rw [show cut + (n + 1) = (cut + n) + 1 by omega, Machine.feedbackState, policy_at, ih]
    exact advance_after source input cut opponent _ _ (by rw [run_history_length]; omega)

variable (active : source.feedback? = some input)

include active in
theorem earlier_body (current : RawCurrent Party Good Technology Instrument)
    (bounded : current.round - source.code.initial.round - 1 < source.history.length + 1 + cut) :
    (target source input cut opponent term).body current = source.body current := by
  unfold Machine.body
  dsimp only [target, Execution.target]
  split
  · rfl
  · split
    · split
      · rfl
      · simp only [Machine.laterResponse, active]
        rw [policy_before source input cut opponent term _ (by omega), complete_state_before source input cut opponent term _ (by omega)]
        exact word_before source input cut opponent _ _ (by rw [history_length]; omega)
    · rfl

include active in
theorem prior_raw_event (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut) :
    ProgrammeSource.rawEvent (target source input cut opponent term).input (ProgrammeHistory.visitAt source.input ordinal).current =
      ProgrammeSource.rawEvent source.input (ProgrammeHistory.visitAt source.input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt source.input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (target source input cut opponent term).body current = source.body current
    apply earlier_body source input cut opponent term active current
    have rounds := ProgrammeHistory.visit_round source.input ordinal
    rw [view] at rounds
    change current.round = source.code.initial.round + ordinal at rounds
    omega

include active in
theorem complete_finance_before (ordinal : Nat) (bounded : ordinal ≤ source.history.length + 2 + cut) :
    Native.Coupling.Match source.code source.input (target source input cut opponent term).input
      (Financial.accountAt source.input ordinal) (Financial.accountAt (target source input cut opponent term).input ordinal) :=
  Native.Coupling.History.complete_accounts source.code source.input (target source input cut opponent term).input rfl rfl
    (source.history.length + 2 + cut) (prior_raw_event source input cut opponent term active)
    source.body (target source input cut opponent term).body rfl rfl ordinal bounded

variable (empty : source.continuation = [])

include empty in
theorem future_word_is_actually_submitted (n : Nat) :
    ((target source input cut opponent term).actualExecution (source.history.length + 1 + (cut + n))).submitted =
      word source.code (Residual.scheduleAt source cut term n) ⟨opponent, input.budget⟩
        (Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩
          (Residual.seed source input cut) n) := by
  rw [(target source input cut opponent term).feedback_word_is_actual (takeover source input cut opponent) rfl empty,
    policy_at, the_whole_future_run_is_the_actual_state]
  simp only [word, decision, if_neg (show ¬(Residual.run source.code (Residual.scheduleAt source cut term)
    ⟨opponent, input.budget⟩ (Residual.seed source input cut) n).history.length < source.history.length + 1 + cut by
      rw [run_history_length]; omega)]

include empty in
private theorem body_at_feedback (current : RawCurrent Party Good Technology Instrument) (n : Nat)
    (rounds : current.round = source.code.initial.round + (source.history.length + 2 + (cut + n))) :
    (target source input cut opponent term).body current =
      word source.code (Residual.scheduleAt source cut term n) ⟨opponent, input.budget⟩
        (Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩
          (Residual.seed source input cut) n) := by
  unfold Machine.body
  rw [rounds]
  have address : source.code.initial.round + (source.history.length + 2 + (cut + n)) -
      source.code.initial.round - 1 = source.history.length + 1 + (cut + n) := by omega
  rw [address, List.getElem?_eq_none (by dsimp only [target, Execution.target]; omega), if_pos (by dsimp only [target, Execution.target]; omega)]
  simp only []
  rw [show source.history.length + 1 + (cut + n) - (target source input cut opponent term).history.length - 1 = cut + n by change source.history.length + 1 + (cut + n) - source.history.length - 1 = cut + n; omega]
  change (match source.continuation[cut + n]? with
    | some word => word
    | none => (target source input cut opponent term).laterResponse current (cut + n)) = _
  rw [empty]
  change word source.code ((target source input cut opponent term).feedbackPolicy (cut + n))
    (takeover source input cut opponent)
    ((target source input cut opponent term).feedbackState (takeover source input cut opponent) (cut + n)) = _
  rw [policy_at, the_whole_future_run_is_the_actual_state]
  simp only [word, decision, if_neg (show ¬(Residual.run source.code (Residual.scheduleAt source cut term)
    ⟨opponent, input.budget⟩ (Residual.seed source input cut) n).history.length < source.history.length + 1 + cut by
      rw [run_history_length]; omega)]

abbrev jointOpponent : Opponent source.code :=
  Residual.respond source.code (Residual.seed source input cut) (Residual.schedules source input cut)
    (Residual.restrict source.code (Residual.seed source input cut) (Residual.schedules source input cut) opponent)

private theorem joint_word (generated : term ∈ Residual.scheduleTerms source input cut)
    (n : Nat) (bounded : n < (Residual.seed source input cut).remaining) :
    word source.code (Residual.scheduleAt source cut term n)
      ⟨jointOpponent source input cut opponent, input.budget⟩
      (Residual.run source.code (Residual.scheduleAt source cut term)
        ⟨jointOpponent source input cut opponent, input.budget⟩ (Residual.seed source input cut) n) =
    word source.code (Residual.scheduleAt source cut term n) ⟨opponent, input.budget⟩
      (Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩ (Residual.seed source input cut) n) := by
  have whole := Residual.one_restriction_preserves_the_whole_remaining_run source.code
    (Residual.seed source input cut) (Residual.schedules source input cut) (Residual.scheduleAt source cut term)
    (List.mem_map.mpr ⟨term, generated, rfl⟩) ⟨opponent, input.budget⟩
  have words := congrArg State.history (whole (n + 1) (by omega))
  simp only [Residual.run, history_keeps_every_actual_word] at words
  rw [whole n (by omega)] at words
  rw [whole n (by omega)]
  exact List.singleton_inj.mp (List.append_cancel_left words)

include active empty in
private theorem joint_prior_raw_event (generated : term ∈ Residual.scheduleTerms source input cut)
    (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut + (Residual.seed source input cut).remaining) :
    ProgrammeSource.rawEvent (target source input cut (jointOpponent source input cut opponent) term).input
        (ProgrammeHistory.visitAt (target source input cut opponent term).input ordinal).current =
      ProgrammeSource.rawEvent (target source input cut opponent term).input
        (ProgrammeHistory.visitAt (target source input cut opponent term).input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt (target source input cut opponent term).input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (target source input cut (jointOpponent source input cut opponent) term).body current =
      (target source input cut opponent term).body current
    have rounds := ProgrammeHistory.visit_round (target source input cut opponent term).input ordinal
    rw [view] at rounds
    change current.round = source.code.initial.round + ordinal at rounds
    by_cases earlier : ordinal < source.history.length + 2 + cut
    · exact (earlier_body source input cut _ term active current (by omega)).trans
        (earlier_body source input cut opponent term active current (by omega)).symm
    · let n := ordinal - (source.history.length + 2 + cut)
      have indexed : ordinal = source.history.length + 2 + (cut + n) := by dsimp only [n]; omega
      rw [body_at_feedback source input cut _ term empty current n (by omega),
        body_at_feedback source input cut opponent term empty current n (by omega)]
      exact joint_word source input cut opponent term generated n (by dsimp only [n]; omega)

include active empty in
/-- A finite joint table has its own native histories with every ordered debt and archive preserved. -/
theorem joint_complete_finance (generated : term ∈ Residual.scheduleTerms source input cut)
    (ordinal : Nat) (bounded : ordinal ≤ source.history.length + 2 + cut + (Residual.seed source input cut).remaining) :
    Native.Coupling.Match source.code (target source input cut opponent term).input
      (target source input cut (jointOpponent source input cut opponent) term).input
      (Financial.accountAt (target source input cut opponent term).input ordinal)
      (Financial.accountAt (target source input cut (jointOpponent source input cut opponent) term).input ordinal) :=
  Native.Coupling.History.complete_accounts source.code (target source input cut opponent term).input
    (target source input cut (jointOpponent source input cut opponent) term).input rfl rfl
    (source.history.length + 2 + cut + (Residual.seed source input cut).remaining)
    (joint_prior_raw_event source input cut opponent term active empty generated)
    (target source input cut opponent term).body
    (target source input cut (jointOpponent source input cut opponent) term).body rfl rfl ordinal bounded

include active empty in
theorem joint_occurrences (generated : term ∈ Residual.scheduleTerms source input cut)
    (ordinal : Nat) (bounded : ordinal < source.history.length + 2 + cut + (Residual.seed source input cut).remaining) :
    (ProgrammeHistory.visitAt (target source input cut (jointOpponent source input cut opponent) term).input ordinal).current =
        (ProgrammeHistory.visitAt (target source input cut opponent term).input ordinal).current ∧
      ProgrammeSource.rawEvent (target source input cut (jointOpponent source input cut opponent) term).input
          (ProgrammeHistory.visitAt (target source input cut (jointOpponent source input cut opponent) term).input ordinal).current =
        ProgrammeSource.rawEvent (target source input cut opponent term).input
          (ProgrammeHistory.visitAt (target source input cut opponent term).input ordinal).current :=
  Native.Coupling.History.occurrences (target source input cut opponent term).input
    (target source input cut (jointOpponent source input cut opponent) term).input rfl rfl
    (source.history.length + 2 + cut + (Residual.seed source input cut).remaining)
    (joint_prior_raw_event source input cut opponent term active empty generated) ordinal bounded

include active empty in
theorem joint_current (generated : term ∈ Residual.scheduleTerms source input cut)
    (ordinal : Nat) (bounded : ordinal ≤ source.history.length + 2 + cut + (Residual.seed source input cut).remaining) :
    (target source input cut (jointOpponent source input cut opponent) term).currentAt ordinal =
      (target source input cut opponent term).currentAt ordinal := by
  have same := Machine.actual_prefix_from_events (target source input cut opponent term).input
    (target source input cut (jointOpponent source input cut opponent) term).input rfl rfl
    (source.history.length + 2 + cut + (Residual.seed source input cut).remaining)
    (joint_prior_raw_event source input cut opponent term active empty generated) ordinal bounded
  unfold Machine.currentAt
  rw [same]
  cases (ProgrammeHistory.visitAt (target source input cut opponent term).input ordinal).current <;> rfl

structure Execution where
  finance_prefix : ∀ ordinal, ordinal ≤ source.history.length + 2 + cut →
    Native.Coupling.Match source.code source.input (target source input cut opponent term).input
      (Financial.accountAt source.input ordinal) (Financial.accountAt (target source input cut opponent term).input ordinal)
  prior_state : (target source input cut opponent term).feedbackState (takeover source input cut opponent) cut =
    source.feedbackState input cut
  complete_states : ∀ n, (target source input cut opponent term).feedbackState (takeover source input cut opponent) (cut + n) =
    Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩ (Residual.seed source input cut) n
  actual_words : ∀ n, ((target source input cut opponent term).actualExecution (source.history.length + 1 + (cut + n))).submitted =
    word source.code (Residual.scheduleAt source cut term n) ⟨opponent, input.budget⟩
      (Residual.run source.code (Residual.scheduleAt source cut term) ⟨opponent, input.budget⟩ (Residual.seed source input cut) n)
  native : (n : Nat) → Native.Disposition (target source input cut opponent term) (source.history.length + 1 + (cut + n))
  native_exact : native = fun n => Native.generate (target source input cut opponent term) (source.history.length + 1 + (cut + n))

include active empty in
def execute : Execution source input cut opponent term where
  finance_prefix := complete_finance_before source input cut opponent term active
  prior_state := complete_state_before source input cut opponent term cut (Nat.le_refl _)
  complete_states := the_whole_future_run_is_the_actual_state source input cut opponent term
  actual_words := future_word_is_actually_submitted source input cut opponent term empty
  native := fun n => Native.generate (target source input cut opponent term) (source.history.length + 1 + (cut + n))
  native_exact := rfl


/-- One future opponent is restricted once across the entire candidate family. -/
structure Disposition where
  table : Residual.Table source.code (Residual.seed source input cut) (Residual.schedules source input cut)
  generated : table ∈ Residual.tables source.code (Residual.seed source input cut) (Residual.schedules source input cut)
  executions : (term : {term : List (Option source.code.Policy) // term ∈ Residual.scheduleTerms source input cut}) →
    Execution source input cut opponent term.val
  table_executions : (term : {term : List (Option source.code.Policy) // term ∈ Residual.scheduleTerms source input cut}) →
    Execution source input cut
      (Residual.respond source.code (Residual.seed source input cut) (Residual.schedules source input cut) table) term.val
  financial_images : (term : {term : List (Option source.code.Policy) // term ∈ Residual.scheduleTerms source input cut}) →
    ∀ ordinal, ordinal ≤ source.history.length + 2 + cut + (Residual.seed source input cut).remaining →
      Native.Coupling.Match source.code (target source input cut opponent term.val).input
        (target source input cut
          (Residual.respond source.code (Residual.seed source input cut) (Residual.schedules source input cut) table) term.val).input
        (Financial.accountAt (target source input cut opponent term.val).input ordinal)
        (Financial.accountAt (target source input cut
          (Residual.respond source.code (Residual.seed source input cut) (Residual.schedules source input cut) table) term.val).input ordinal)
  joint_executions : (term : {term : List (Option source.code.Policy) // term ∈ Residual.scheduleTerms source input cut}) →
    ∀ n ≤ (Residual.seed source input cut).remaining,
      (target source input cut opponent term.val).feedbackState (takeover source input cut opponent) (cut + n) =
        Residual.run source.code (Residual.scheduleAt source cut term.val)
          ⟨Residual.respond source.code (Residual.seed source input cut) (Residual.schedules source input cut) table, input.budget⟩
          (Residual.seed source input cut) n

include active empty in
def generate : Disposition source input cut opponent where
  table := Residual.restrict source.code (Residual.seed source input cut) (Residual.schedules source input cut) opponent
  generated := Residual.restriction_is_generated source.code (Residual.seed source input cut) (Residual.schedules source input cut) opponent
  executions := fun term => execute source input cut opponent term.val active empty
  table_executions := fun term => execute source input cut (jointOpponent source input cut opponent) term.val active empty
  financial_images := fun term => joint_complete_finance source input cut opponent term.val active empty term.property
  joint_executions := fun term n bounded =>
    (the_whole_future_run_is_the_actual_state source input cut opponent term.val n).trans
      (Residual.one_restriction_preserves_the_whole_remaining_run source.code (Residual.seed source input cut)
        (Residual.schedules source input cut) _ (List.mem_map.mpr ⟨term.val, term.property, rfl⟩)
        ⟨opponent, input.budget⟩ n bounded).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Future
