import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.State
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Payment

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {domain : List (Cursor model.source.code)} {original : Prefix.Rule model.source.code}
  {baseline : Program model.source.code (horizon domain)} {actualHorizon : Nat}
  (state : State model domain original baseline actualHorizon)
  (reader : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)

abbrev request := Charge.fee quote
abbrev attempt := Replay.inspect reader (request quote) (state.current point rival) rival
abbrev funded := Cut.Ready reader (attempt state reader quote point rival)
abbrev requestedRule (supported : request quote ∈ words model.source.code.actions model.source.code.actionLimit) :=
  Replay.protocol reader (request quote) supported

/-- The new solver is invoked only behind this stage's own resource receipt.
The stage is already part of the cached complete plan, including on refusal. -/
def produce (supported : request quote ∈ words model.source.code.actions model.source.code.actionLimit)
    (booked : state.Booked (requestedRule reader quote supported))
    (_paid : Charge.paid quote model reader (state.current point rival) rival
      (Charge.endAt quote model reader (state.current point rival) rival)) :=
  (state.carry (requestedRule reader quote supported) booked).inspect reader

inductive Turn where
  | unsupported (outside : request quote ∉ words model.source.code.actions model.source.code.actionLimit)
  | unreserved (supported : request quote ∈ words model.source.code.actions model.source.code.actionLimit)
      (missing : ¬ state.Booked (requestedRule reader quote supported))
  | unpaid (supported : request quote ∈ words model.source.code.actions model.source.code.actionLimit)
      (booked : state.Booked (requestedRule reader quote supported))
      (missing : ¬ funded state reader quote point rival)
  | paid (supported : request quote ∈ words model.source.code.actions model.source.code.actionLimit)
      (booked : state.Booked (requestedRule reader quote supported))
      (receipt : funded state reader quote point rival)
      (decision : (state.carry (requestedRule reader quote supported) booked).Decision reader)

def turn : Turn state reader quote point rival :=
  if supported : request quote ∈ words model.source.code.actions model.source.code.actionLimit then
    if booked : state.Booked (requestedRule reader quote supported) then
      if paid : funded state reader quote point rival then
        .paid supported booked paid (produce state reader quote point rival supported booked
          (Payment.a_ready_actual_request_generates_its_own_charge_receipt model reader quote _ rival paid))
      else .unpaid supported booked paid
    else .unreserved supported booked
  else .unsupported supported

namespace Turn
variable {state reader quote point rival}

def next : Turn state reader quote point rival → State model domain original baseline actualHorizon
  | .unsupported _ | .unreserved _ _ => state
  | .unpaid supported booked _ => state.carry (requestedRule reader quote supported) booked
  | .paid supported booked _ decision =>
      let carried := state.carry (requestedRule reader quote supported) booked
      carried.commit reader (observation (carried.current point rival) reader) decision

def rules : Turn state reader quote point rival → List (Prefix.Rule model.source.code)
  | .unsupported _ | .unreserved _ _ => []
  | .unpaid supported _ _ | .paid supported _ _ _ => [requestedRule reader quote supported]

def learned : Turn state reader quote point rival → Bool
  | .paid .. => true
  | _ => false

theorem every_learning_turn_has_its_own_actual_payment (event : Turn state reader quote point rival)
    (advanced : event.learned = true) : funded state reader quote point rival := by
  cases event with
  | paid supported booked receipt decision => exact receipt
  | unsupported | unreserved | unpaid => cases advanced

theorem each_learning_turn_releases_a_fresh_source_indexed_charge
    (event : Turn state reader quote point rival) (advanced : event.learned = true) :
    Charge.paid quote model reader (state.current point rival) rival
      (Charge.endAt quote model reader (state.current point rival) rival) :=
  Payment.a_ready_actual_request_generates_its_own_charge_receipt model reader quote _ rival
    (every_learning_turn_has_its_own_actual_payment event advanced)

theorem no_unpaid_turn_runs_the_new_solver (event : Turn state reader quote point rival)
    (missing : ¬ funded state reader quote point rival) : event.next.programme = state.programme := by
  cases event with
  | unsupported | unreserved | unpaid => rfl
  | paid supported booked receipt decision => exact False.elim (missing receipt)

theorem every_reserved_stage_keeps_its_actual_attempt_on_refusal (event : Turn state reader quote point rival) :
    event.next.past = state.past ++ event.rules := by
  cases event with
  | unsupported | unreserved => exact (List.append_nil _).symm
  | unpaid => rfl
  | paid supported booked receipt decision =>
      exact State.committing_the_stored_decision_preserves_all_paid_past _ _ _ decision

theorem every_turn_is_the_same_actual_source_update (event : Turn state reader quote point rival) :
    event.next.current point rival = Window.Observed.Transcript.actualView event.rules (state.current point rival) rival := by
  change Window.Observed.Transcript.actualView event.next.past point rival = _
  rw [every_reserved_stage_keeps_its_actual_attempt_on_refusal]
  unfold Window.Observed.Transcript.actualView
  rw [List.foldl_append]
  rfl

theorem actual_knowledge_survives_every_paid_or_refused_turn
    (event : Turn state reader quote point rival)
    (covered : Knowledge.Contains state.beliefs (state.current point rival)) :
    Knowledge.Contains event.next.beliefs (event.next.current point rival) := by
  cases event with
  | unsupported | unreserved => exact covered
  | unpaid supported booked missing =>
      have next := Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
        [requestedRule reader quote supported] state.beliefs (state.current point rival) covered rival
      change Knowledge.Contains _ (Evidence.after (state.current point rival) _ rival) at next
      rw [←State.carrying_a_reserved_request_is_the_actual_next_stage state _ booked point rival] at next
      exact next
  | paid supported booked receipt decision =>
      let carried := state.carry (requestedRule reader quote supported) booked
      have next := Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain
        [requestedRule reader quote supported] state.beliefs (state.current point rival) covered rival
      change Knowledge.Contains _ (Evidence.after (state.current point rival) _ rival) at next
      rw [←State.carrying_a_reserved_request_is_the_actual_next_stage state _ booked point rival] at next
      have observed := Rolling.Receipt.the_actual_local_record_generates_its_own_covered_planning_domain
        carried.beliefs (carried.current point rival) next reader
      change Knowledge.Contains (carried.commit reader _ decision).beliefs ((carried.commit reader _ decision).current point rival)
      cases decision <;> exact observed

end Turn
end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid
