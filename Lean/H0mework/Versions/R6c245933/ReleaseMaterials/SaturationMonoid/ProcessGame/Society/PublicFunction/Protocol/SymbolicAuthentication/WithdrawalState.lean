import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWithdrawal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalState

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

def step (ownerStart budget : Nat) (state : State code) (rule : Rule code) (rival : Opponent code) :=
  Reaction.Feedback.advance code (some rule.work.val) ⟨driver code ownerStart rule rival, budget⟩ state

def run (ownerStart budget : Nat) (state : State code) : List (EventHistory.Stage (code := code)) → State code
  | [] => state
  | (rule, rival) :: tail => run ownerStart budget (step ownerStart budget state rule rival) tail

theorem actual_state (cursor : Cursor code) (past : List (EventHistory.Stage (code := code))) :
    run cursor.ownerStart cursor.entry.budget (EventStep.seed cursor) past = EventStep.seed (EventHistory.execute cursor past) := by
  induction past generalizing cursor with
  | nil => rfl
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    have next := ih (cursor.after rule rival)
    rw [EventStep.actual_next_state] at next
    exact next

def replies (ownerStart : Nat) (state : State code) : List (Move code) :=
  match Distributed.Recall.Information.Agency.ownerAt code ownerStart state.history.length with
  | some _ => [none]
  | none => moves code

def advance (ownerStart budget : Nat) (states : List (State code)) (rule : Rule code) :=
  states.flatMap fun state => (replies ownerStart state).map fun reply => step ownerStart budget state rule (EventStep.fixed reply)

def history (ownerStart budget : Nat) (states : List (State code)) : List (Rule code) → List (State code)
  | [] => states
  | rule :: tail => history ownerStart budget (advance ownerStart budget states rule) tail

omit [DecidableEq Port] [DecidableEq Technology] in
theorem actual_is_generated (ownerStart budget : Nat) (states : List (State code)) (state : State code)
    (inside : state ∈ states) (past : List (EventHistory.Stage (code := code))) :
    run ownerStart budget state past ∈ history ownerStart budget states (past.map Prod.fst) := by
  induction past generalizing states state with
  | nil => exact inside
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    apply ih
    apply List.mem_flatMap.mpr
    refine ⟨state, inside, List.mem_map.mpr ?_⟩
    cases own : Distributed.Recall.Information.Agency.ownerAt code ownerStart state.history.length with
    | none => exact ⟨rival state.history state.past state.frame, by simp only [replies, own]; exact every_move_is_generated code _, rfl⟩
    | some worker =>
      refine ⟨none, by simp only [replies, own]; exact List.mem_cons_self, ?_⟩
      simp only [step, Reaction.Feedback.advance, word, decision, driver, own]

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem generated_has_a_run (ownerStart budget : Nat) (rules : List (Rule code))
    (states : List (State code)) (state : State code)
    (inside : state ∈ history ownerStart budget states rules) :
    ∃ initial ∈ states, ∃ stages : List (EventHistory.Stage (code := code)),
      stages.map Prod.fst = rules ∧ run ownerStart budget initial stages = state := by
  induction rules generalizing states with
  | nil => exact ⟨state, inside, [], rfl, rfl⟩
  | cons rule rules ih =>
    obtain ⟨middle, generated, stages, selected, actual⟩ := ih (advance ownerStart budget states rule) inside
    obtain ⟨initial, original, mapped⟩ := List.mem_flatMap.mp generated
    obtain ⟨reply, _, same⟩ := List.mem_map.mp mapped
    subst middle
    exact ⟨initial, original, (rule, EventStep.fixed reply) :: stages, by simp [selected], actual⟩

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (installed : List (Rule model.source.code))

def domain := history start.ownerStart start.entry.budget [EventStep.seed start] installed

theorem every_actual_prefix_is_in_the_generated_state_domain
    (past : List (EventHistory.Stage (code := model.source.code))) :
    EventStep.seed (EventHistory.execute start past) ∈ domain model start (past.map Prod.fst) := by
  rw [← actual_state]
  exact actual_is_generated _ _ _ _ List.mem_cons_self past

theorem every_generated_state_has_its_actual_full_source
    (state : State model.source.code) (inside : state ∈ domain model start installed) :
    ∃ stages : List (EventHistory.Stage (code := model.source.code)), stages.map Prod.fst = installed ∧
      EventStep.seed (EventHistory.execute start stages) = state := by
  obtain ⟨initial, original, stages, selected, actual⟩ := generated_has_a_run _ _ installed [EventStep.seed start] state inside
  have same := List.mem_singleton.mp original
  subst initial
  exact ⟨stages, selected, (actual_state start stages).symm.trans actual⟩

def fibre (worker : Fin model.source.code.sites) (signal : Fin model.source.code.signals) :=
  (domain model start installed).filter fun state => state.frame.inbox worker == signal
abbrev request (state : State model.source.code) (worker : Fin model.source.code.sites) :=
  Mandate.request model.scope state.current (model.source.code.siteParty worker) .revoke

theorem mem_fibre (worker : Fin model.source.code.sites) (signal : Fin model.source.code.signals)
    (state : State model.source.code) :
    state ∈ fibre model start installed worker signal ↔ state ∈ domain model start installed ∧ state.frame.inbox worker = signal := by
  simp [fibre]

variable (worker : Fin model.source.code.sites) (signal : Fin model.source.code.signals)

inductive Query where
  | unseen (empty : fibre model start installed worker signal = [])
  | ready (value : Request Party Good Port (Mandate.State Party Technology) Instrument) (first : State model.source.code)
      (actual : first ∈ fibre model start installed worker signal) (exact : request model first worker = value)
      (uniform : ∀ other ∈ fibre model start installed worker signal, request model other worker = value)
  | ambiguous (first second : State model.source.code)
      (left : first ∈ fibre model start installed worker signal) (right : second ∈ fibre model start installed worker signal)
      (different : request model second worker ≠ request model first worker)

def query : Query model start installed worker signal :=
  match selected : fibre model start installed worker signal with
  | [] => .unseen selected
  | first :: rest =>
    match inspect (fun other => request model other worker = request model first worker) rest with
    | .accepted uniform => .ready (request model first worker) first
        (by rw [selected]; exact List.mem_cons_self) rfl (by
          intro other member
          rw [selected] at member
          rcases List.mem_cons.mp member with same | later
          · exact same ▸ rfl
          · exact uniform other later)
    | .rejected other member different => .ambiguous first other
        (by rw [selected]; exact List.mem_cons_self) (by rw [selected]; exact List.mem_cons_of_mem _ member) different

inductive Result where
  | unseen
  | ambiguous (first second : State model.source.code)
  | blocked (reason : LocalWithdrawal.Obstruction)
  | ready (value : Request Party Good Port (Mandate.State Party Technology) Instrument)

def produce : Result model :=
  match query model start installed worker signal with
  | .unseen _ => .unseen
  | .ambiguous first second .. => .ambiguous first second
  | .ready value .. =>
    if model.source.code.siteParty worker ∉ Delegation.members model.scope.task then .blocked .notMember else
    if ¬ 1 ≤ model.source.code.actionLimit then .blocked .noCapacity else
    if Event.activate worker ∉ model.source.code.eventAlphabet then .blocked .unsupportedActivation else
    if model.source.code.memoryReady signal ≠ true then .blocked .sealed else
    if value ∉ model.source.code.actions then .blocked .unsupportedAction else .ready value

def value? : Result model → Option (Request Party Good Port (Mandate.State Party Technology) Instrument)
  | .ready value => some value
  | _ => none

theorem ready_of_value (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : value? model (produce model start installed worker signal) = some value) :
    produce model start installed worker signal = .ready value := by
  cases selected : produce model start installed worker signal <;> simp_all [value?]

theorem ready_admission (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : produce model start installed worker signal = .ready value) :
    1 ≤ model.source.code.actionLimit ∧ value ∈ model.source.code.actions ∧ Event.activate worker ∈ model.source.code.eventAlphabet ∧
      model.source.code.memoryReady signal = true ∧ model.source.code.siteParty worker ∈ Delegation.members model.scope.task := by
  unfold produce at prepared
  cases selected : query model start installed worker signal with
  | unseen empty => simp only [selected] at prepared; contradiction
  | ambiguous first second left right different => simp only [selected] at prepared; contradiction
  | ready candidate first actual precise uniform =>
    simp only [selected] at prepared
    split_ifs at prepared
    simp_all

theorem a_ready_query_recovers_the_actual_original_revoke
    (past : List (EventHistory.Stage (code := model.source.code)))
    (value : Request Party Good Port (Mandate.State Party Technology) Instrument)
    (prepared : produce model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) = .ready value) :
    value = NativeReview.action model start past worker := by
  have actual : EventStep.seed (EventHistory.execute start past) ∈ fibre model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) :=
    (mem_fibre model start _ _ _ _).mpr ⟨every_actual_prefix_is_in_the_generated_state_domain model start past, rfl⟩
  unfold produce at prepared
  cases selected : query model start (past.map Prod.fst) worker
      (LocalWithdrawal.reading model (EventHistory.execute start past) worker) with
  | unseen empty => simp only [selected] at prepared; contradiction
  | ambiguous first second left right different => simp only [selected] at prepared; contradiction
  | ready candidate first generated precise uniform =>
    simp only [selected] at prepared
    split_ifs at prepared
    cases prepared
    exact (uniform _ actual).symm

theorem ambiguity_retains_two_actual_compatible_states
    (first second : State model.source.code)
    (result : produce model start installed worker signal = .ambiguous first second) :
    first ∈ domain model start installed ∧ second ∈ domain model start installed ∧
      first.frame.inbox worker = second.frame.inbox worker ∧ request model second worker ≠ request model first worker := by
  unfold produce at result
  cases selected : query model start installed worker signal with
  | unseen empty => simp only [selected] at result; contradiction
  | ready candidate witness actual precise uniform =>
    simp only [selected] at result
    split_ifs at result
  | ambiguous left right one two different =>
    simp only [selected] at result
    cases result
    have a := (mem_fibre model start installed worker signal first).mp one
    have b := (mem_fibre model start installed worker signal second).mp two
    exact ⟨a.1, b.1, a.2.trans b.2.symm, different⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalState
