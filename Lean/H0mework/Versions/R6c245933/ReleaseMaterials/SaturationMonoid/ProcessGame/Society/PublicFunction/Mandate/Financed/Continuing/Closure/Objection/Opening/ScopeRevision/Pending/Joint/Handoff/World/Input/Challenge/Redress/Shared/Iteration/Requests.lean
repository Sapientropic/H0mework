import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Execution
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Sovereignty
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Runtime.Readback

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Input.Event Input.Event.Future.Expiry.Progress
noncomputable section

structure Cursor where
  saved : Packet
  pending : List Action

def initial (packet : Packet) : Cursor := ⟨packet,[]⟩
def submitted (cursor : Cursor) (incoming : List Action) := cursor.pending ++ incoming

/-- One cached report receives the old residual and new raw input at the saved
actual epoch; the original joint source consumes that report's full endpoint. -/
structure Result (cursor : Cursor) (incoming : List Action) where
  private mk ::
  report : Input.Recovery.Metering.Assessment.Report cursor.saved.2 (submitted cursor incoming)
  report_exact : report = Input.Recovery.Metering.Assessment.Runtime.read cursor.saved.2 (submitted cursor incoming)
  disposition : Iteration.Step report.packet.2
  disposition_exact : disposition = Iteration.produce report.packet.2

def produce (cursor : Cursor) (incoming : List Action) : Result cursor incoming :=
  let report := Input.Recovery.Metering.Assessment.Runtime.read cursor.saved.2 (submitted cursor incoming)
  ⟨report,rfl,Iteration.produce report.packet.2,rfl⟩

namespace Result
variable {cursor : Cursor} {incoming : List Action} (made : Result cursor incoming)

def next : Cursor := ⟨made.disposition.packet,made.report.residual⟩
def native : Evolution cursor.saved made.next.saved :=
  .append (made.report.native (.same cursor.saved)) made.disposition.native

def finance := Response.financeAlong made.native
def costs := Event.Costs.cost made.native
def accounts := Event.Funding.account made.native

def original (row : Responsibility.Row cursor.saved) := Responsibility.transport made.native row

def rawOrigins := made.report.staged.endpoint.remainingOrigins

theorem unresolved_requests_keep_their_original_raw_refusal_positions :
    made.rawOrigins.map (fun origin => origin.item.request) = made.next.pending :=
  made.report.staged.endpoint.every_remaining_position_retains_its_original_failed_identity

theorem old_residual_precedes_new_input (later : List Action) :
    submitted made.next later = made.report.residual ++ later := rfl

theorem the_received_word_and_all_actual_repair_bills_are_retained :
    ∃ suffix, made.report.staged.endpoint.saved.inputs =
      cursor.saved.2.inputs ++ [submitted cursor incoming] ++ suffix :=
  made.report.staged.endpoint.extension

theorem every_old_responsibility_keeps_its_origin_and_complete_history
    (row : Responsibility.Row cursor.saved) :
    (made.original row).row.origin = row.origin ∧
      row.state.history <+: (made.original row).state.history ∧
      Nonempty ((made.original row).native.Run row.origin.initial (made.original row).state) :=
  ⟨(Responsibility.every_actual_step_retains_its_original_admission_and_history made.native row).1,
    (Responsibility.every_actual_step_retains_its_original_admission_and_history made.native row).2,
    ⟨(made.original row).complete⟩⟩

theorem all_newborn_responsibilities_are_in_the_actual_final_census
    (row : Responsibility.Row made.next.saved) : row ∈ Responsibility.census made.next.saved :=
  Responsibility.every_original_row_is_in_the_census row

theorem material_balance_in_the_complete_received_window (bearer : Bool) (good : Good) :
    (World.current made.next.saved.1 made.next.saved.2.inputs).stock bearer good +
      made.costs bearer (.operating good) + made.costs bearer (.debtPayment good) =
    (World.current cursor.saved.1 cursor.saved.2.inputs).stock bearer good +
      Event.Costs.credits made.native bearer good :=
  Event.Costs.material_balance made.native bearer good

theorem cash_and_every_original_debt_share_the_same_received_window (bearer : Bool) (good : Good) :
    made.accounts true bearer good + made.accounts false bearer good =
      Event.FinancialBalance.quotedNet cursor.saved bearer good -
        Event.FinancialBalance.quotedNet made.next.saved bearer good :=
  Event.Funding.actual_net_position_change made.native bearer good

/-- The future receipt belongs to this joint source at the received endpoint,
not to the old epoch or a separately executed Future closure. -/
def future := Sovereignty.future made.report.packet.2

theorem an_active_received_endpoint_calls_its_own_scope_joint_source
    (active : Responsibility.settled made.report.packet = false) :
    made.next.saved = (Shared.Runtime.answer made.report.packet.2).packet := by
  change made.disposition.packet = _
  have actual := congrArg (Iteration.Step.packet made.report.packet.2) made.disposition_exact
  have generated := congrArg (Iteration.Step.packet made.report.packet.2)
    (Iteration.active_calls_the_same_joint_source (epoch := made.report.packet.1) made.report.packet.2 active)
  exact actual.trans generated

theorem terminal_means_complete_native_receipts
    (terminal : made.disposition.isTerminal = true) :
    Responsibility.WholeTerminationReceipt made.report.packet :=
  Iteration.Step.termination _ made.disposition terminal

theorem the_received_joint_source_consumes_future_rows_matrix_and_own_next
    (active : Responsibility.settled made.report.packet = false) :
    made.next.saved = (Shared.Runtime.answer made.report.packet.2).packet ∧
    Sovereignty.NoPublicAbsorbingSink made.report.packet.2 ∧
    Sovereignty.NoFinalAuthorityCertificate made.report.packet.2 ∧
    Nonempty (Sovereignty.FutureReceipt made.report.packet.2) ∧
    Financial.Family.ledgerClaims sources made.next.saved.2.finance.current =
      (World.current made.next.saved.1 made.next.saved.2.inputs).claims ∧
    HEq (Iteration.activation made.report.packet.2).tick.generated.wholeLedgerWriteBack
      ((Iteration.activation made.report.packet.2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Iteration.activation made.report.packet.2).current.visit.current) ∧
    (Iteration.activation made.report.packet.2).tick.nextCurrent =
      (Iteration.facade made.report.packet.2).process.stateAt
        ((Iteration.facade made.report.packet.2).process.successor (Iteration.activation made.report.packet.2).state) := by
  let own := Sovereignty.generate made.report.packet.2
  refine ⟨made.an_active_received_endpoint_calls_its_own_scope_joint_source active,
    own.noSink,own.noFinal,⟨own.outlook⟩,?_,own.joint.ledger,own.joint.next⟩
  rw [made.an_active_received_endpoint_calls_its_own_scope_joint_source active]
  exact own.joint.matrix
end Result

inductive Run : Cursor → List (List Action) → Type where
  | private observed (cursor : Cursor) : Run cursor []
  | private received (cursor : Cursor) (incoming : List Action) {later : List (List Action)}
      (made : Result cursor incoming) (exact : made = produce cursor incoming)
      (tail : Run made.next later) : Run cursor (incoming::later)

def receive (cursor : Cursor) : (inputs : List (List Action)) → Run cursor inputs
  | [] => .observed cursor
  | incoming::later =>
      let made := produce cursor incoming
      .received cursor incoming made rfl (receive made.next later)

namespace Run
variable {cursor : Cursor} {inputs : List (List Action)}

def finish : {cursor : Cursor} → {inputs : List (List Action)} → Run cursor inputs → Cursor
  | _,_,.observed cursor => cursor
  | _,_,.received _ _ _ _ tail => tail.finish

def native (run : Run cursor inputs) : Evolution cursor.saved run.finish.saved := by
  induction run
  next cursor => exact .same _
  next cursor incoming later made exact tail path => exact .append made.native path

def finance (run : Run cursor inputs) := Response.financeAlong run.native

def visits : {cursor : Cursor} → {inputs : List (List Action)} → Run cursor inputs →
    List (Sigma fun state : Cursor => Sigma fun incoming : List Action => Result state incoming)
  | _,_,.observed _ => []
  | _,_,.received cursor incoming made _ tail => ⟨cursor,incoming,made⟩ :: tail.visits

theorem every_incoming_word_is_actually_received (run : Run cursor inputs) :
    run.visits.map (fun visit => visit.2.1) = inputs := by
  induction run
  next cursor => rfl
  next cursor incoming later made exact tail ih => exact congrArg (incoming :: ·) ih

theorem every_visit_is_generated (run : Run cursor inputs)
    (visit : Sigma fun state : Cursor => Sigma fun incoming : List Action => Result state incoming)
    (inside : visit ∈ run.visits) : visit.2.2 = produce visit.1 visit.2.1 := by
  induction run
  next cursor => cases inside
  next cursor incoming laterInputs made same tail ih =>
      rcases List.mem_cons.mp inside with sameVisit | later
      · cases sameVisit
        exact same
      · exact ih later

theorem no_observation_cut_erases_the_original_responsibility (run : Run cursor inputs)
    (row : Responsibility.Row cursor.saved) :
    (Responsibility.transport run.native row).row.origin = row.origin ∧
      row.state.history <+: (Responsibility.transport run.native row).state.history ∧
      Nonempty ((Responsibility.transport run.native row).native.Run row.origin.initial
        (Responsibility.transport run.native row).state) :=
  ⟨(Responsibility.every_actual_step_retains_its_original_admission_and_history run.native row).1,
    (Responsibility.every_actual_step_retains_its_original_admission_and_history run.native row).2,
    ⟨(Responsibility.transport run.native row).complete⟩⟩
end Run

/-- Each autonomous step re-reads its own saved packet's source emission. -/
def tick (cursor : Cursor) := produce cursor (Input.Event.Future.ownWord cursor.saved.2)

def after (cursor : Cursor) : Nat → Cursor
  | 0 => cursor
  | count+1 => (tick (after cursor count)).next

def native (cursor : Cursor) : (count : Nat) → Evolution cursor.saved (after cursor count).saved
  | 0 => .same _
  | count+1 => .append (native cursor count) (tick (after cursor count)).native

theorem every_autonomous_input_is_emitted_by_its_actual_saved_source (cursor : Cursor) (count : Nat) :
    Input.Event.Future.ownWord (after cursor count).saved.2 =
      ((after cursor count).saved.1.source.decideAt
        (World.current (after cursor count).saved.1 (after cursor count).saved.2.inputs)
        (OutstandingSource.History.trailAt (after cursor count).saved.1.source
          (after cursor count).saved.2.inputs ((after cursor count).saved.2.inputs.length+2)).frame.payments).word :=
  Input.Event.Future.own_word_is_generated_by_the_actual_residual _

theorem every_actual_autonomous_cut_consumes_its_own_scope_future_and_root
    (cursor : Cursor) (count : Nat)
    (active : Responsibility.settled (tick (after cursor count)).report.packet = false) :
    let made := tick (after cursor count)
    made.next.saved = (Shared.Runtime.answer made.report.packet.2).packet ∧
    Sovereignty.NoPublicAbsorbingSink made.report.packet.2 ∧
    Sovereignty.NoFinalAuthorityCertificate made.report.packet.2 ∧
    Nonempty (Sovereignty.FutureReceipt made.report.packet.2) ∧
    Financial.Family.ledgerClaims sources made.next.saved.2.finance.current =
      (World.current made.next.saved.1 made.next.saved.2.inputs).claims ∧
    HEq (Iteration.activation made.report.packet.2).tick.generated.wholeLedgerWriteBack
      ((Iteration.activation made.report.packet.2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Iteration.activation made.report.packet.2).current.visit.current) ∧
    (Iteration.activation made.report.packet.2).tick.nextCurrent =
      (Iteration.facade made.report.packet.2).process.stateAt
        ((Iteration.facade made.report.packet.2).process.successor (Iteration.activation made.report.packet.2).state) :=
  (tick (after cursor count)).the_received_joint_source_consumes_future_rows_matrix_and_own_next active

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests.Native
open Input.Event

def evolution : {cursor : Cursor} → {inputs : List (List Action)} → (run : Run cursor inputs) →
    Evolution cursor.saved run.finish.saved
  | _,_,.observed cursor => .same cursor.saved
  | _,_,.received _ _ made _ tail => .append made.native (evolution tail)

theorem evolution_exact {cursor : Cursor} {inputs : List (List Action)} (run : Run cursor inputs) :
    evolution run = run.native := by
  induction run
  next cursor => rfl
  next cursor incoming later made actual tail ih =>
    simp only [evolution,Run.native,ih]

@[csimp] theorem evolution_codegen : @Run.native = @evolution := by
  funext cursor inputs run
  exact (evolution_exact run).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests.Native
