import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

variable (code : Code Party Good Port Technology Instrument)

abbrev Need := code.Key → Bool

def localEvents (site : Fin code.sites) (reading : Bool) : List (Reaction.Choice code) :=
  code.eventAlphabet.attach.filter fun event => match reading, event.val with
    | true, .send sender _ => decide (sender = site)
    | false, .activate worker => decide (worker = site)
    | _, _ => false

def localChoice (need : Need code) (site : Fin code.sites) (signal : Fin code.signals) : Move code :=
  (localEvents code site (need (site,signal))).head?

omit [DecidableEq Port] [DecidableEq Technology] in
theorem generated_local_event_belongs_to_its_worker (site : Fin code.sites) (reading : Bool)
    (event : Reaction.Choice code) (inside : event ∈ localEvents code site reading) :
    match reading, event.val with
    | true, .send sender _ => sender = site
    | false, .activate worker => worker = site
    | _, _ => False := by
  rcases event with ⟨event, supported⟩
  have selected := (List.mem_filter.mp inside).2
  cases reading <;> cases event <;> simp only [Bool.false_eq_true, decide_eq_true_eq] at selected <;> exact selected

omit [DecidableEq Port] [DecidableEq Technology] in
theorem missing_local_event_is_a_complete_typed_wait (need : Need code) (site : Fin code.sites)
    (signal : Fin code.signals) : localChoice code need site signal = none ↔
      localEvents code site (need (site,signal)) = [] := by
  simp only [localChoice, List.head?_eq_none_iff]

/-- Public round-robin ownership alternates with unrestricted environment turns. -/
def ownerAt (start length : Nat) : Option (Fin code.sites) :=
  if positive : 0 < code.sites then
    if (length - start) % 2 = 0 then
      some ⟨((length-start)/2) % code.sites, Nat.mod_lt _ positive⟩
    else none
  else none

def externalChoice (move : Move code) : Move code := match move with
  | none => none
  | some event => match event.val with
    | .adversary _ | .deliver _ => some event
    | .send _ _ | .activate _ => none

omit [DecidableEq Port] [DecidableEq Technology] in
theorem external_input_cannot_impersonate_a_workers_event (move : Move code) (event : Reaction.Choice code)
    (accepted : externalChoice code move = some event) :
    match event.val with
    | .adversary _ | .deliver _ => True
    | .send _ _ | .activate _ => False := by
  cases move with
  | none => cases accepted
  | some attempt =>
    rcases attempt with ⟨attempt, supported⟩
    cases attempt <;> simp only [externalChoice, Option.some.injEq, reduceCtorEq] at accepted
    all_goals subst event; trivial

def driver (start : Nat) (need : Need code) (rival : Opponent code) : Opponent code :=
  fun history past frame => match ownerAt code start history.length with
    | some site => localChoice code need site (frame.inbox site)
    | none => externalChoice code (rival history past frame)

omit [DecidableEq Port] [DecidableEq Technology] in
theorem own_turn_is_independent_of_the_environment (start : Nat) (need : Need code)
    (first second : Opponent code) (history : History) (past : Events code) (frame : code.Frame)
    (site : Fin code.sites) (owned : ownerAt code start history.length = some site) :
    driver code start need first history past frame = localChoice code need site (frame.inbox site) ∧
      driver code start need first history past frame = driver code start need second history past frame := by
  simp only [driver, owned, and_self]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem equal_local_record_generates_the_same_own_event (start : Nat) (need : Need code)
    (first second : Opponent code) (history : History) (past : Events code)
    (left right : code.Frame) (site : Fin code.sites)
    (owned : ownerAt code start history.length = some site)
    (same : left.inbox site = right.inbox site) :
    driver code start need first history past left = driver code start need second history past right := by
  simp only [driver, owned, same]

omit [DecidableEq Port] [DecidableEq Technology] in
theorem every_environment_turn_checks_the_same_actual_adaptive_attempt (start : Nat) (need : Need code)
    (rival : Opponent code) (history : History) (past : Events code) (frame : code.Frame)
    (external : ownerAt code start history.length = none) :
    driver code start need rival history past frame = externalChoice code (rival history past frame) := by
  simp only [driver, external]

variable (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat) (need : Need source.code) (rival : Opponent source.code)

abbrev start := source.history.length + 1 + cut
abbrev controller := driver source.code (start source cut) need rival
abbrev term := List.replicate (source.feedbackState input cut).remaining (some source.reference)
abbrev target := Future.target source input cut (controller source cut need rival) (term source input cut)
abbrev targetInput := Future.takeover source input cut (controller source cut need rival)
abbrev state (n : Nat) := (target source input cut need rival).feedbackState (targetInput source input cut need rival) (cut+n)

theorem every_control_is_originally_generated : term source input cut ∈ Residual.scheduleTerms source input cut := by
  apply (mem_sequences_iff _ _ _).mpr
  constructor
  · simp only [term, List.length_replicate, le_refl]
  · intro control inside
    have same := (List.mem_replicate.mp inside).2
    subst control
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨source.reference,source.reference_generated,rfl⟩

theorem active_control_is_the_original_work_policy (n : Nat)
    (bounded : n < (source.feedbackState input cut).remaining) :
    Residual.scheduleAt source cut (term source input cut) n = some source.reference := by
  simp only [Residual.scheduleAt, term, List.getElem?_replicate, if_pos bounded, Option.getD_some]

theorem own_decision_is_generated_from_the_actual_local_record
    (n : Nat) (bounded : n < (source.feedbackState input cut).remaining)
    (site : Fin source.code.sites)
    (owned : ownerAt source.code (start source cut) (state source input cut need rival n).history.length = some site) :
    decision source.code (targetInput source input cut need rival) (state source input cut need rival n) =
      localChoice source.code need site ((state source input cut need rival n).frame.inbox site) := by
  have complete := Future.the_whole_future_run_is_the_actual_state source input cut
    (controller source cut need rival) (term source input cut) n
  have remaining : (state source input cut need rival n).remaining = (source.feedbackState input cut).remaining - n :=
    (congrArg State.remaining complete).trans (Residual.remaining_is_the_seed_budget _ _ _ _ _)
  have historyLength : (state source input cut need rival n).history.length = source.history.length+1+cut+n := by
    have historyAt : ∀ (machine : Machine Party Good Port (Mandate.State Party Technology) Instrument)
        (entry : Input machine.code) (index : Nat),
        (machine.feedbackState entry index).history.length = machine.history.length+1+index := by
      intro machine entry index
      induction index with
      | zero => simp [Machine.feedbackState, Machine.feedbackInitial]
      | succ index ih =>
        change (advance machine.code _ _ _).history.length = _
        rw [history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
        omega
    exact (historyAt (target source input cut need rival) _ (cut+n)).trans (by change source.history.length+1+(cut+n) = _; omega)
  have active : (state source input cut need rival n).remaining ≠ 0 := by omega
  simp only [decision, if_neg active]
  change (if _ then _ else _) = _
  rw [if_neg (by rw [historyLength]; omega)]
  exact (own_turn_is_independent_of_the_environment source.code (start source cut) need rival rival _ _ _ site owned).1

theorem actual_own_read_submits_the_original_fee
    (empty : source.continuation = []) (n : Nat)
    (bounded : n < (source.feedbackState input cut).remaining)
    (site recipient : Fin source.code.sites)
    (owned : ownerAt source.code (start source cut) (state source input cut need rival n).history.length = some site)
    (event : Reaction.Choice source.code)
    (chosen : localChoice source.code need site ((state source input cut need rival n).frame.inbox site) = some event)
    (reading : event.val = .send site recipient) :
    ((target source input cut need rival).actualExecution (source.history.length+1+(cut+n))).submitted = source.code.sendCost site recipient := by
  rw [(target source input cut need rival).feedback_word_is_actual (targetInput source input cut need rival) rfl empty,
    Execution.policy_at]
  change word source.code (Residual.scheduleAt source cut (term source input cut) n) _ _ = _
  rw [active_control_is_the_original_work_policy source input cut n bounded]
  change word source.code (some source.reference) (targetInput source input cut need rival) (state source input cut need rival n) = _
  simp only [word, own_decision_is_generated_from_the_actual_local_record source input cut need rival n bounded site owned, chosen]
  simp only [stepLocal, reading, Code.step, List.nil_append]

theorem actual_own_wait_keeps_provenance_and_consumes_a_cut
    (empty : source.continuation = []) (n : Nat)
    (bounded : n < (source.feedbackState input cut).remaining)
    (site : Fin source.code.sites)
    (owned : ownerAt source.code (start source cut) (state source input cut need rival n).history.length = some site)
    (waiting : localChoice source.code need site ((state source input cut need rival n).frame.inbox site) = none) :
    ((target source input cut need rival).actualExecution (source.history.length+1+(cut+n))).submitted = [] ∧
      (state source input cut need rival (n+1)).history = (state source input cut need rival n).history ++ [[]] ∧
      (state source input cut need rival (n+1)).remaining = (state source input cut need rival n).remaining - 1 := by
  have chosen := own_decision_is_generated_from_the_actual_local_record source input cut need rival n bounded site owned
  have noWord : word source.code (some source.reference) (targetInput source input cut need rival)
      (state source input cut need rival n) = [] := by simp only [word, chosen, waiting]
  have policy : (target source input cut need rival).feedbackPolicy (cut+n) = some source.reference :=
    (Execution.policy_at {source with feedback? := some (targetInput source input cut need rival)} cut (term source input cut) n).trans (active_control_is_the_original_work_policy source input cut n bounded)
  refine ⟨?_,?_,?_⟩
  · rw [(target source input cut need rival).feedback_word_is_actual (targetInput source input cut need rival) rfl empty, policy]
    exact noWord
  · change (advance source.code ((target source input cut need rival).feedbackPolicy (cut+n))
        (targetInput source input cut need rival) (state source input cut need rival n)).history = _
    rw [policy, history_keeps_every_actual_word, noWord]
  · change (advance source.code _ _ _).remaining = _
    rfl

def informationNeed
    (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (budget : Nat)
    (reference : Program bound budget) : Need bound.source.code := fun key =>
  match Information.compile bound budget key.1 key.2 reference with
  | .selected _ => false
  | .blocked _ => true


theorem precise_information_blockage_generates_a_local_read_request
    (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (budget : Nat)
    (reference : Program bound budget) (site : Fin bound.source.code.sites)
    (signal : Fin bound.source.code.signals)
    (rejected : ∀ programme : Program bound budget, Information.Rejection bound budget site signal reference programme)
    (blocked : Information.compile bound budget site signal reference = .blocked rejected) :
    localChoice bound.source.code (informationNeed bound budget reference) site signal =
      (localEvents bound.source.code site true).head? := by
  simp only [localChoice, informationNeed, blocked]


end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency
