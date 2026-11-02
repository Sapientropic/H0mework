import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Execution

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Service
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Prefix.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (quotas : List Nat) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code) (ordinal : Nat)


variable (selected : Reservation.Selection model domain original reference worker receiver quote quotas slots point rival ordinal)
  (initial : List (View (code := model.source.code)))

abbrev past := reserved model original worker quote quotas ++ selected.plan.announcements
abbrev before := Window.Observed.Transcript.actualView
  (past model domain original reference worker receiver quote quotas slots point rival ordinal selected) point rival

def seed : Publication.Learning.Paid.State model domain original selected.plan.choice.policy.protocol (Deployment.actualHorizon model point) where
  past := past model domain original reference worker receiver quote quotas slots point rival ordinal selected
  programme := selected.plan.choice.policy.protocol
  beliefs := Window.Observed.Transcript.publicViews
    (past model domain original reference worker receiver quote quotas slots point rival ordinal selected) initial
  within := by
    have room := selected.domainRoom
    simp only [past,List.length_append,List.length_replicate];omega
  actualWithin := by
    have room := selected.actualRoom
    simp only [past,List.length_append,List.length_replicate];omega
  retained := by
    simpa only [past,List.length_append,List.length_replicate] using
      (Plan.eligible_iff model domain original reference worker quote quotas selected.plan.announcements selected.plan.choice.policy).mp selected.plan.publicationPrefix
  above := Prefix.Commitment.admissible_plan_is_its_own_valid_reference model domain original reference _ selected.plan.choice.policy.accepted

theorem the_paid_cache_generates_its_own_next_fee_and_learning_reservation :
    (seed model domain original reference worker receiver quote quotas slots point rival ordinal selected initial).Booked
      (Publication.Learning.Paid.requestedRule receiver quote selected.supported) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [seed,past,List.length_append,List.length_replicate] using selected.actualRoom
  · simpa only [seed,past,List.length_append,List.length_replicate] using selected.domainRoom
  · have kept := (Reservation.eligible_iff model domain original reference worker receiver quote quotas selected.plan.announcements selected.plan.choice.policy).mp selected.reservedNext
    simpa only [seed,past,Reservation.reservedBlock,Reservation.fee,Charge.feeRule,dif_pos selected.supported,
      Publication.Learning.Paid.requestedRule,List.length_append,List.length_replicate] using kept

theorem the_unconditioned_public_successors_keep_the_actual_source
    (covered : Knowledge.Contains initial point) :
    Knowledge.Contains (seed model domain original reference worker receiver quote quotas slots point rival ordinal selected initial).beliefs
      ((seed model domain original reference worker receiver quote quotas slots point rival ordinal selected initial).current point rival) :=
  Window.Observed.Transcript.every_actual_past_keeps_a_representative_in_the_same_public_domain _ initial point covered rival

include initial in
theorem the_request_origin_is_the_actual_selected_communication_cut
    (made : Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal = some selected) :
    (before model domain original reference worker receiver quote quotas slots point rival ordinal selected).point =
      Reservation.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal selected.plan.announcements.length := by
  have actual := Publication.Learning.Paid.State.current_is_the_actual_control_prefix
    (seed model domain original reference worker receiver quote quotas slots point rival ordinal selected initial) point rival
  change (before model domain original reference worker receiver quote quotas slots point rival ordinal selected).point = _ at actual
  have comm := Execution.the_actual_communication_cut_is_the_paid_source_followed_by_the_registered_programme model domain original reference worker receiver quote quotas slots point rival ordinal selected made
  change Reservation.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal selected.plan.announcements.length = _ at comm
  rw [actual,comm]
  have ready := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
    selected.plan.execution selected.plan.finished selected.plan.arrived
  obtain ⟨_,paid,_⟩ := Segmented.a_released_result_has_executed_the_entire_fixed_fee_plan
    model domain original reference worker quote quotas point rival selected.plan.finished ready
  change Deployment.paidFinal model domain original reference worker quote quotas point rival = _ at paid
  rw [paid]
  change Splice.install point.point rival (past model domain original reference worker receiver quote quotas slots point rival ordinal selected) = _
  unfold past Splice.install
  rw [List.foldl_append]

abbrev attempt := Replay.inspect receiver (Charge.fee quote)
  (before model domain original reference worker receiver quote quotas slots point rival ordinal selected) rival

inductive Admission where
  | ready (available : Cut.Ready receiver (attempt model domain original reference worker receiver quote quotas slots point rival ordinal selected))
      (paid : Charge.paid quote model receiver
        (before model domain original reference worker receiver quote quotas slots point rival ordinal selected) rival
        (Charge.endAt quote model receiver (before model domain original reference worker receiver quote quotas slots point rival ordinal selected) rival))
  | blocked (missing : ¬ Cut.Ready receiver (attempt model domain original reference worker receiver quote quotas slots point rival ordinal selected))

def admission : Admission model domain original reference worker receiver quote quotas slots point rival ordinal selected :=
  if ready : Cut.Ready receiver (attempt model domain original reference worker receiver quote quotas slots point rival ordinal selected) then
    .ready ready (Publication.Learning.Paid.Payment.a_ready_actual_request_generates_its_own_charge_receipt model receiver quote _ rival ready)
  else .blocked ready

inductive Outcome where
  | blocked (reason : Reservation.Blocked model domain original reference worker receiver quote quotas slots point rival ordinal)
  | selected (selection : Reservation.Selection model domain original reference worker receiver quote quotas slots point rival ordinal)
      (checked : Admission model domain original reference worker receiver quote quotas slots point rival ordinal selection)

def generate : Outcome model domain original reference worker receiver quote quotas slots point rival ordinal :=
  match made : Reservation.select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => .blocked (Reservation.obstruction model domain original reference worker receiver quote quotas slots point rival ordinal made)
  | some selection => .selected selection (admission model domain original reference worker receiver quote quotas slots point rival ordinal selection)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Reservation.Service
