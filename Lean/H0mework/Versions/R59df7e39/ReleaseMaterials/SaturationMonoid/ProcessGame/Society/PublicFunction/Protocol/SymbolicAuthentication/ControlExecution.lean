import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptFold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlExecution

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

inductive CallData (Key Move : Type) where
  | stopped
  | inherited (attempt : Move)
  | own (site : Key) (attempt : Move)
  | external (attempt : Move)
  deriving DecidableEq

abbrev Call (code : Code Party Good Port (Mandate.State Party Technology) Instrument) :=
  CallData (Fin code.sites) (Move code)

def admitted (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : Call code → Move code
  | .stopped => none
  | .inherited attempt | .own _ attempt => attempt
  | .external attempt => Distributed.Recall.Information.Agency.externalChoice code attempt

def suppressed (code : Code Party Good Port (Mandate.State Party Technology) Instrument) : Call code → Bool
  | .external (some event) => match event.val with
    | .send _ _ | .activate _ => true
    | _ => false
  | _ => false

variable (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (input : Input source.code) (cut : Nat)
  (protocol : Distributed.Recall.Information.Agency.Protocol.Rule source.code)
  (rival : Opponent source.code)

abbrev actual := OwnedAttestation.actual source input cut protocol rival
abbrev original (n : Nat) := AttestationTransport.state source input cut protocol rival n
abbrev originalInput := AttestationTransport.actualInput source input cut protocol rival

/-- The only callback invocation of a material step is here. The returned
value is retained before the original interface guard is applied. -/
def capture (state : Feedback.State source.code) : Call source.code :=
  if state.remaining = 0 then .stopped
  else if state.history.length < source.history.length + 1 + cut then
    .inherited (input.opponent state.history state.past state.frame)
  else match Distributed.Recall.Information.Agency.ownerAt source.code
      (Distributed.Recall.Information.Agency.start source cut) state.history.length with
    | some site => .own site (Distributed.Recall.Information.Agency.Protocol.localEvent source.code protocol site (state.frame.inbox site))
    | none => .external (rival state.history state.past state.frame)

theorem captured_admission_is_the_original_decision (state : Feedback.State source.code) :
    admitted source.code (capture source input cut protocol rival state) =
      decision source.code (originalInput source input cut protocol rival) state := by
  unfold capture
  split_ifs with stopped earlier
  · simp only [admitted, decision, stopped, if_true]
  · simp only [admitted, decision, if_neg stopped, if_pos earlier]
  · simp only [admitted, decision, if_neg stopped, if_neg earlier,
      Distributed.Recall.Information.Agency.Protocol.controller, Distributed.Recall.Information.Agency.Protocol.driver]
    cases Distributed.Recall.Information.Agency.ownerAt source.code
      (Distributed.Recall.Information.Agency.start source cut) state.history.length <;> rfl

theorem captured_external_has_actual_control_and_callback
    (state : Feedback.State source.code) (attempt : Move source.code)
    (external : capture source input cut protocol rival state = .external attempt) :
    state.remaining ≠ 0 ∧ source.history.length + 1 + cut ≤ state.history.length ∧
      Distributed.Recall.Information.Agency.ownerAt source.code
        (Distributed.Recall.Information.Agency.start source cut) state.history.length = none ∧
      rival state.history state.past state.frame = attempt := by
  unfold capture at external
  split_ifs at external; try contradiction
  split at external; try contradiction
  rename_i owned
  exact ⟨by assumption, by omega, owned, CallData.external.inj external⟩

@[ext] structure Occurrence where
  ordinal : Nat
  before : Feedback.State source.code
  call : Call source.code
  submitted : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  after : Feedback.State source.code

structure State where
  core : Feedback.State source.code
  events : List (Occurrence source)

def seed : State source := ⟨original source input cut protocol rival 0, []⟩

/-- `advance` receives a constant selected move, so it cannot invoke the raw
callback again. This creates the audit and the state transition together. -/
def step (n : Nat) (previous : State source) : State source :=
  let call := capture source input cut protocol rival previous.core
  let selected : Input source.code := ⟨fun _ _ _ => admitted source.code call, input.budget⟩
  let policy := (actual source input cut protocol rival).feedbackPolicy (cut + n)
  let submitted := word source.code policy selected previous.core
  let next := advance source.code policy selected previous.core
  ⟨next, previous.events ++ [⟨n, previous.core, call, submitted, next⟩]⟩

private theorem selected_decision (state : Feedback.State source.code) :
    decision source.code ⟨fun _ _ _ => admitted source.code (capture source input cut protocol rival state), input.budget⟩ state =
      decision source.code (originalInput source input cut protocol rival) state := by
  by_cases stopped : state.remaining = 0
  · simp only [decision, stopped, if_true]
  · simpa only [decision, if_neg stopped] using captured_admission_is_the_original_decision source input cut protocol rival state

theorem step_projects_to_the_original_transition (n : Nat) (previous : State source) :
    (step source input cut protocol rival n previous).core =
      advance source.code ((actual source input cut protocol rival).feedbackPolicy (cut + n))
        (originalInput source input cut protocol rival) previous.core := by
  unfold step
  dsimp only
  simp only [advance, word, selected_decision]

def run : Nat → State source
  | 0 => seed source input cut protocol rival
  | n + 1 => step source input cut protocol rival n (run n)

theorem run_projects_to_the_same_actual_state (n : Nat) :
    (run source input cut protocol rival n).core = original source input cut protocol rival n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, step_projects_to_the_original_transition, ih]
    change _ = (actual source input cut protocol rival).feedbackState
      (originalInput source input cut protocol rival) (cut + (n + 1))
    rw [show cut + (n + 1) = (cut + n) + 1 by omega, Machine.feedbackState]

theorem actual_states_factor_through_admitted_control (other : Opponent source.code)
    (same : Distributed.Recall.Information.Agency.Protocol.controller source cut protocol rival =
      Distributed.Recall.Information.Agency.Protocol.controller source cut protocol other) (n : Nat) :
    original source input cut protocol rival n = original source input cut protocol other n :=
  congrArg (fun driver : Opponent source.code =>
    (show Feedback.State source.code from
      (Future.target source input cut driver
        (Distributed.Recall.Information.Agency.Protocol.term source input cut protocol).val).feedbackState
          (Future.takeover source input cut driver) (cut + n))) same

private theorem history_length (machine : Machine Party Good Port (Mandate.State Party Technology) Instrument)
    (entry : Input machine.code) (index : Nat) :
    (machine.feedbackState entry index).history.length = machine.history.length + 1 + index := by
  induction index with
  | zero => simp only [Machine.feedbackState, Machine.feedbackInitial, List.length_append,
      List.length_singleton]
  | succ index ih =>
    change (advance machine.code _ _ _).history.length = _
    rw [history_keeps_every_actual_word, List.length_append, List.length_singleton, ih]
    omega

theorem original_history_length (n : Nat) :
    (original source input cut protocol rival n).history.length = source.history.length + 1 + cut + n := by
  exact (history_length (actual source input cut protocol rival)
    (originalInput source input cut protocol rival) (cut + n)).trans (by
      change source.history.length + 1 + (cut + n) = _
      omega)

theorem original_remaining (n : Nat) :
    (original source input cut protocol rival n).remaining = (source.feedbackState input cut).remaining - n :=
  (congrArg Feedback.State.remaining (Future.the_whole_future_run_is_the_actual_state source input cut
    (Distributed.Recall.Information.Agency.Protocol.controller source cut protocol rival)
    (Distributed.Recall.Information.Agency.Protocol.term source input cut protocol).val n)).trans
    (Residual.remaining_is_the_seed_budget _ _ _ _ _)

theorem original_reception_factors_through_admitted_control (other : Opponent source.code)
    (same : Distributed.Recall.Information.Agency.Protocol.controller source cut protocol rival =
      Distributed.Recall.Information.Agency.Protocol.controller source cut protocol other)
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (encoding : AttestationTransport.Encoding source) (law : AttestationReception.ReceptionLaw source)
    (receiver : Fin source.code.sites) (horizon : Nat) :
    AttestationReception.run source input cut protocol rival vocabulary encoding law receiver horizon =
      AttestationReception.run source input cut protocol other vocabulary encoding law receiver horizon := by
  induction horizon with
  | zero => rfl
  | succ n ih =>
    simp only [AttestationReception.run, ih]
    delta AttestationReception.receive AttestationReception.incoming
      AttestationReception.check AttestationReception.deliveredAt AttestationReception.matchingPacket
      AttestationTransport.verify AttestationTransport.issuedAt AttestationTransport.outgoing
      AttestationTransport.move OwnedAttestation.verify OwnedAttestation.issuedAt
      OwnedAttestation.inspect OwnedAttestation.owner AttestationTransport.state OwnedAttestation.localState
      Distributed.Recall.Information.Agency.Protocol.state AttestationTransport.actualInput
      AttestationTransport.execution OwnedAttestation.execution OwnedAttestation.actual
      Distributed.Recall.Information.Agency.Protocol.targetInput
      Distributed.Recall.Information.Agency.Protocol.target
    generalize left : Distributed.Recall.Information.Agency.Protocol.controller source cut protocol rival = first at same ⊢
    generalize right : Distributed.Recall.Information.Agency.Protocol.controller source cut protocol other = second at same ⊢
    cases same
    -- Generated matchers retain raw callback parameters until their bodies unfold.
    set_option smartUnfolding false in
      rfl


def occurrence (n : Nat) : Occurrence source :=
  ⟨n, original source input cut protocol rival n,
    capture source input cut protocol rival (original source input cut protocol rival n),
    word source.code ((actual source input cut protocol rival).feedbackPolicy (cut + n))
      (originalInput source input cut protocol rival) (original source input cut protocol rival n),
    original source input cut protocol rival (n + 1)⟩

theorem generated_events_are_the_actual_coupled_occurrences (horizon : Nat) :
    (run source input cut protocol rival horizon).events =
      (List.range horizon).map (occurrence source input cut protocol rival) := by
  induction horizon with
  | zero => rfl
  | succ n ih =>
    rw [run]
    unfold step
    dsimp only
    rw [ih, run_projects_to_the_same_actual_state]
    simp only [List.range_succ, List.map_append, List.map_singleton]
    congr 1
    apply congrArg List.singleton
    apply Occurrence.ext
    · rfl
    · rfl
    · rfl
    · simp only [occurrence, word, selected_decision]
    · exact (step_projects_to_the_original_transition source input cut protocol rival n
        ⟨original source input cut protocol rival n, []⟩).trans (by
          change advance source.code _ _ _ = (actual source input cut protocol rival).feedbackState
            (originalInput source input cut protocol rival) (cut + (n + 1))
          rw [show cut + (n + 1) = (cut + n) + 1 by omega, Machine.feedbackState])

theorem no_occurrence_is_lost_or_duplicated (horizon : Nat) :
    ((run source input cut protocol rival horizon).events.map Occurrence.ordinal) = List.range horizon := by
  rw [generated_events_are_the_actual_coupled_occurrences, List.map_map]
  exact List.map_id _

theorem events_are_preserved (horizon : Nat) :
    (run source input cut protocol rival horizon).events <+:
      (run source input cut protocol rival (horizon + 1)).events :=
  List.prefix_append _ _

theorem external_record_has_the_original_callback_origin (horizon : Nat) (record : Occurrence source)
    (inside : record ∈ (run source input cut protocol rival horizon).events) (attempt : Move source.code)
    (external : record.call = .external attempt) :
    record.before.remaining ≠ 0 ∧ source.history.length + 1 + cut ≤ record.before.history.length ∧
      Distributed.Recall.Information.Agency.ownerAt source.code
        (Distributed.Recall.Information.Agency.start source cut) record.before.history.length = none ∧
      rival record.before.history record.before.past record.before.frame = attempt := by
  rw [generated_events_are_the_actual_coupled_occurrences] at inside
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp inside
  exact captured_external_has_actual_control_and_callback source input cut protocol rival
    (original source input cut protocol rival n) attempt external

theorem every_record_has_original_word_and_literal_next (empty : source.continuation = [])
    (horizon : Nat) (record : Occurrence source)
    (inside : record ∈ (run source input cut protocol rival horizon).events) :
    record.ordinal < horizon ∧ record = occurrence source input cut protocol rival record.ordinal ∧
      record.before.current = (AttestationTransport.execution source input cut protocol rival record.ordinal).before ∧
      record.submitted = (AttestationTransport.execution source input cut protocol rival record.ordinal).submitted ∧
      record.after.current = (AttestationTransport.execution source input cut protocol rival record.ordinal).after ∧
      record.after.current = source.code.law.next record.before.current record.submitted := by
  rw [generated_events_are_the_actual_coupled_occurrences] at inside
  obtain ⟨n, bounded, rfl⟩ := List.mem_map.mp inside
  have next : (original source input cut protocol rival (n + 1)).current =
      source.code.law.next (original source input cut protocol rival n).current
        (occurrence source input cut protocol rival n).submitted := by
    change ((actual source input cut protocol rival).feedbackState (originalInput source input cut protocol rival) (cut + (n + 1))).current = _
    rw [show cut + (n + 1) = (cut + n) + 1 by omega, Machine.feedbackState]
    rfl
  have before := (ReceiptFold.before_is_feedback source input cut protocol rival empty n).symm
  have submitted := (ReceiptFold.word_is_feedback source input cut protocol rival empty n).symm
  refine ⟨List.mem_range.mp bounded, rfl, before, submitted, ?_, next⟩
  change (original source input cut protocol rival (n + 1)).current =
    (AttestationTransport.execution source input cut protocol rival n).after
  rw [next, before, show (occurrence source input cut protocol rival n).submitted =
    (AttestationTransport.execution source input cut protocol rival n).submitted from submitted,
    (AttestationTransport.execution source input cut protocol rival n).after_exact]
  rfl

theorem original_request_audit_consumes_the_generated_occurrence (empty : source.continuation = [])
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (horizon : Nat) (record : Occurrence source)
    (inside : record ∈ (run source input cut protocol rival horizon).events) :
    (OwnedAttestation.audit source input cut protocol rival vocabulary record.ordinal).map
      (fun row => row.1.request) = record.submitted := by
  rw [OwnedAttestation.every_original_request_is_retained]
  exact (every_record_has_original_word_and_literal_next source input cut protocol rival empty horizon record inside).2.2.2.1.symm

def refusals (horizon : Nat) : List (Occurrence source) :=
  (run source input cut protocol rival horizon).events.filter fun event => suppressed source.code event.call

theorem refused_external_attempt_cannot_create_work_or_packets
    (horizon : Nat) (record : Occurrence source)
    (inside : record ∈ refusals source input cut protocol rival horizon) :
    record.submitted = [] ∧ record.after.frame = record.before.frame ∧ record.after.past = record.before.past ∧
      record.after.current = source.code.law.next record.before.current [] := by
  obtain ⟨member, rejected⟩ := List.mem_filter.mp inside
  rw [generated_events_are_the_actual_coupled_occurrences] at member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  have selected := captured_admission_is_the_original_decision source input cut protocol rival
    (original source input cut protocol rival n)
  change suppressed source.code (capture source input cut protocol rival
    (original source input cut protocol rival n)) = true at rejected
  have noAdmission : admitted source.code (capture source input cut protocol rival
      (original source input cut protocol rival n)) = none := by
    generalize capture source input cut protocol rival (original source input cut protocol rival n) = call at rejected ⊢
    cases call with
    | stopped => cases rejected
    | inherited attempt => cases rejected
    | own site attempt => cases rejected
    | external attempt =>
      cases attempt with
      | none => cases rejected
      | some event =>
        rcases event with ⟨event, supported⟩
        cases event <;> simp_all [suppressed, admitted, Distributed.Recall.Information.Agency.externalChoice]
  have noDecision : decision source.code (originalInput source input cut protocol rival)
      (original source input cut protocol rival n) = none := selected.symm.trans noAdmission
  dsimp only [occurrence]
  change word source.code _ _ _ = [] ∧ _ ∧ _ ∧ _
  simp only [word, noDecision]
  rw [show original source input cut protocol rival (n + 1) =
    advance source.code ((actual source input cut protocol rival).feedbackPolicy (cut + n))
      (originalInput source input cut protocol rival) (original source input cut protocol rival n) by
        change (actual source input cut protocol rival).feedbackState _ (cut + (n + 1)) = _
        rw [show cut + (n + 1) = (cut + n) + 1 by omega, Machine.feedbackState]]
  simp only [advance, word, noDecision]
  cases (actual source input cut protocol rival).feedbackPolicy (cut + n) <;> exact ⟨rfl, rfl, rfl, rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlExecution
