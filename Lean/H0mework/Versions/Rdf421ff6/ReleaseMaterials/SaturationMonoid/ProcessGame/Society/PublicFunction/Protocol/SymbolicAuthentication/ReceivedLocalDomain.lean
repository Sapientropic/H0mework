import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptObservation

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedLocalDomain

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}


open CommunicationObservation

theorem compact_row (left right : Cursor code) (same : EventStep.Matches left right)
    (rule : Rule code) (rival : Opponent code) :
    Same (StageTrace.material left rule (EventStep.fixed (CausalLocalDomain.chosen left right rival)))
      (StageTrace.material right rule rival) := by
  have next := CausalLocalDomain.a_compact_reply_preserves_the_entire_actual_completed_prefix rule left right same rival
  have word : (StageTrace.material left rule (EventStep.fixed (CausalLocalDomain.chosen left right rival))).submitted =
      (StageTrace.material right rule rival).submitted := by
    have histories := congrArg (fun state : State code => state.history) next.state
    rw [EventStep.actual_next_state, EventStep.actual_next_state] at histories
    simp only [history_keeps_every_actual_word] at histories
    have before := congrArg (fun state : State code => state.history) same.state
    rw [before] at histories
    exact (StageTrace.material_is_the_actual_step _ _ _).2.trans
      ((List.singleton_inj.mp (List.append_cancel_left histories)).trans (StageTrace.material_is_the_actual_step _ _ _).2.symm)
  have owned : StageTrace.activation (StageTrace.material left rule (EventStep.fixed (CausalLocalDomain.chosen left right rival))) =
      StageTrace.activation (StageTrace.material right rule rival) := by
    by_cases stopped : (EventStep.seed right).remaining = 0
    · simp only [StageTrace.activation, StageTrace.material, StageTrace.capture, same.state, if_pos stopped]
    · simp only [StageTrace.activation, StageTrace.material, StageTrace.capture, same.state, same.ownerStart, if_neg stopped]
      cases Distributed.Recall.Information.Agency.ownerAt code right.ownerStart (EventStep.seed right).history.length <;> rfl
  refine ⟨same.cut, same.state, word, ?_, owned, ?_, ?_⟩
  · exact (StageTrace.material_is_the_actual_step _ _ _).1.trans
      (next.state.trans (StageTrace.material_is_the_actual_step _ _ _).1.symm)
  · by_cases stopped : (EventStep.seed right).remaining = 0
    · simp only [StageTransport.outgoing, StageTrace.material, StageTrace.capture, same.state, if_pos stopped]
    · simp only [StageTransport.outgoing, StageTrace.material, StageTrace.capture, same.state, same.ownerStart, if_neg stopped]
      cases Distributed.Recall.Information.Agency.ownerAt code right.ownerStart (EventStep.seed right).history.length <;> rfl
  · by_cases stopped : (EventStep.seed right).remaining = 0
    · simp only [StageTransport.admission, StageTrace.material, StageTrace.capture, same.state, if_pos stopped]
    · simp only [StageTransport.admission, StageTrace.material, StageTrace.capture, same.state, same.ownerStart, if_neg stopped]
      cases own : Distributed.Recall.Information.Agency.ownerAt code right.ownerStart (EventStep.seed right).history.length with
      | some site => rfl
      | none =>
        simp [ControlExecution.admitted, CausalLocalDomain.chosen, same.state, same.ownerStart, own,
          EventStep.fixed, EventStep.selected, CausalLocalDomain.external_choice_is_idempotent]

variable (start : Cursor code)

abbrev current (trace : List (EventHistory.Stage (code := code))) := EventHistory.execute start trace

def Compatible (left right : List (EventHistory.Stage (code := code))) : Prop :=
  EventStep.Matches (current start left) (current start right) ∧
    Related (StageTrace.records start left) (StageTrace.records start right)

def advance (rule : Rule code) (domain : List (List (EventHistory.Stage (code := code)))) :=
  domain.flatMap fun trace => (CausalLocalDomain.replies (current start trace)).map fun reply =>
    trace ++ [(rule, EventStep.fixed reply)]

def history : List (List (EventHistory.Stage (code := code))) → List (Rule code) → List (List (EventHistory.Stage (code := code)))
  | domain, [] => domain
  | domain, rule :: tail => history (advance start rule domain) tail

theorem compact_extension (left right : List (EventHistory.Stage (code := code)))
    (same : Compatible start left right) (rule : Rule code) (rival : Opponent code) :
    Compatible start
      (left ++ [(rule, EventStep.fixed (CausalLocalDomain.chosen (current start left) (current start right) rival))])
      (right ++ [(rule, rival)]) := by
  constructor
  · simpa only [current, StageQueue.execute_append, EventHistory.execute] using
      CausalLocalDomain.a_compact_reply_preserves_the_entire_actual_completed_prefix rule _ _ same.1 rival
  · rw [StageQueue.records_append, StageQueue.records_append]
    exact List.rel_append same.2 (List.Forall₂.cons (compact_row _ _ same.1 rule rival) List.Forall₂.nil)

theorem coverage_from (domain : List (List (EventHistory.Stage (code := code))))
    (left right : List (EventHistory.Stage (code := code))) (inside : left ∈ domain)
    (same : Compatible start left right) (suffix : List (EventHistory.Stage (code := code))) :
    ∃ representative ∈ history start domain (suffix.map Prod.fst), Compatible start representative (right ++ suffix) := by
  induction suffix generalizing domain left right with
  | nil => exact ⟨left, inside, by simpa only [List.append_nil] using same⟩
  | cons stage tail ih =>
    rcases stage with ⟨rule, rival⟩
    have admitted : CausalLocalDomain.chosen (current start left) (current start right) rival ∈
        CausalLocalDomain.replies (current start left) := by
      unfold CausalLocalDomain.chosen CausalLocalDomain.replies
      split
      · simp
      · exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨EventStep.selected (current start right) rival, every_move_is_generated code _, rfl⟩)
    have generated : left ++ [(rule, EventStep.fixed (CausalLocalDomain.chosen (current start left) (current start right) rival))] ∈
        advance start rule domain := List.mem_flatMap.mpr ⟨left, inside, List.mem_map.mpr ⟨_, admitted, rfl⟩⟩
    obtain ⟨representative, member, related⟩ := ih _ _ _ generated (compact_extension start left right same rule rival)
    exact ⟨representative, member, by simpa only [List.append_assoc, List.singleton_append] using related⟩

def domain (installed : List (Rule code)) := history start [[]] installed

theorem actual_prefix_coverage (stages : List (EventHistory.Stage (code := code))) :
    ∃ representative ∈ domain start (stages.map Prod.fst), Compatible start representative stages := by
  obtain ⟨representative, inside, same⟩ := coverage_from start [[]] [] [] (List.mem_singleton_self _)
    ⟨EventStep.matches_self _, List.Forall₂.nil⟩ stages
  exact ⟨representative, inside, same⟩

theorem generated_representative_preserves_every_real_receipt
    (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
    (stages : List (EventHistory.Stage (code := code))) :
    ∃ representative ∈ domain start (stages.map Prod.fst),
      EventStep.Matches (current start representative) (current start stages) ∧
      ∀ receiver count, RequestReadback.produce vocabulary encoding law start representative receiver count =
        RequestReadback.produce vocabulary encoding law start stages receiver count := by
  obtain ⟨representative, inside, state, rows⟩ := actual_prefix_coverage start stages
  exact ⟨representative, inside, state, fun receiver count =>
    ReceiptObservation.produce_equal vocabulary encoding law start representative stages rows receiver count⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceivedLocalDomain
