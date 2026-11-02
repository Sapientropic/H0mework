import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Installation
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Selected
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestReadback

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Receipt
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

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
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code)

abbrev Plan := Publication.Plan.Selection model domain original reference worker receiver quote quotas slots point rival ordinal

def stages (plan : Selected.Plan model domain original reference worker receiver quote quotas slots point rival ordinal) :
    List (EventHistory.Stage (code := model.source.code)) :=
  (reserved model original worker quote quotas ++ plan.announcements).map (fun rule => (rule,rival))

def observed (plan : Selected.Plan model domain original reference worker receiver quote quotas slots point rival ordinal) :=
  RequestReadback.produce vocabulary encoding law point.point
    (stages model domain original reference worker receiver quote quotas slots point rival ordinal plan) receiver
    (stages model domain original reference worker receiver quote quotas slots point rival ordinal plan).length

def Addresses (closing : PaidSlot model worker quote rival) (receipt : RequestReadback.Receipt (code := model.source.code)) : Prop :=
  receipt.statement.ballot.cut = closing.before.point.cut ∧ receipt.statement.ballot.key = worker ∧
    (Charge.fee quote)[receipt.statement.ballot.position]? = some receipt.statement.request

instance (closing : PaidSlot model worker quote rival) (receipt : RequestReadback.Receipt (code := model.source.code)) :
    Decidable (Addresses model worker quote rival closing receipt) := by unfold Addresses;infer_instance

structure Published where
  plan : Plan model domain original reference worker receiver quote quotas slots point rival ordinal
  selected : Publication.Plan.select model domain original reference worker receiver quote quotas slots point rival ordinal = some plan
  closing : PaidSlot model worker quote rival
  sealed : (Segmented.trace model domain original reference worker quote quotas point rival).closingReceipt = some closing
  receipt : RequestReadback.Receipt (code := model.source.code)
  received : receipt ∈ (observed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law plan).receipts
  addressed : Addresses model worker quote rival closing receipt

structure Pending where
  plan : Plan model domain original reference worker receiver quote quotas slots point rival ordinal
  selected : Publication.Plan.select model domain original reference worker receiver quote quotas slots point rival ordinal = some plan
  closing : PaidSlot model worker quote rival
  sealed : (Segmented.trace model domain original reference worker quote quotas point rival).closingReceipt = some closing
  absent : ∀ receipt ∈ (observed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law plan).receipts,
    ¬ Addresses model worker quote rival closing receipt

inductive Outcome where
  | noSelectedProgramme (reason : Publication.Plan.Blocked model domain original reference worker receiver quote quotas slots point rival ordinal)
  | pending (residual : Pending model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)
  | published (record : Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

/-- The packet identifies an actual paid completion occurrence. The programme is
resolved from that same public source/cache, not encoded into a caller's signal. -/
def generate : Outcome model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law :=
  match selected : Publication.Plan.select model domain original reference worker receiver quote quotas slots point rival ordinal with
  | none => .noSelectedProgramme (Publication.Plan.obstruction model domain original reference worker receiver quote quotas slots point rival ordinal selected)
  | some plan =>
    match sealed : (Segmented.trace model domain original reference worker quote quotas point rival).closingReceipt with
    | none => False.elim (by
        have ready := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
          plan.execution plan.finished plan.arrived
        obtain ⟨_,closing,present⟩ := Segmented.a_released_finished_cache_is_its_actual_payment_replay_and_has_a_closing_receipt
          model domain original reference worker quote quotas point rival plan.finished ready
        rw [sealed] at present
        cases present)
    | some closing =>
      match found : (observed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law plan).receipts.find?
          (fun receipt => decide (Addresses model worker quote rival closing receipt)) with
      | none => .pending ⟨plan,selected,closing,sealed,by
          intro receipt inside
          simpa only [decide_eq_true_eq] using (List.find?_eq_none.mp found) receipt inside⟩
      | some receipt => .published ⟨plan,selected,closing,sealed,receipt,List.mem_of_find?_eq_some found,
          of_decide_eq_true (List.find?_some
            (p := fun candidate : RequestReadback.Receipt (code := model.source.code) =>
              decide (Addresses model worker quote rival closing candidate)) found)⟩

def resolve (incoming : RequestReadback.Receipt (code := model.source.code)) :
    Option (Prefix.Choice model domain original (reserved model original worker quote quotas) reference) :=
  match generate model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law with
  | .published record => if incoming = record.receipt then some record.plan.choice else none
  | _ => none

theorem resolve_uses_only_the_received_address_in_the_generated_source
    (incoming : RequestReadback.Receipt (code := model.source.code))
    (choice : Prefix.Choice model domain original (reserved model original worker quote quotas) reference)
    (resolved : resolve model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law incoming = some choice) :
    ∃ record, generate model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law = .published record ∧
      incoming = record.receipt ∧ choice = record.plan.choice := by
  unfold resolve at resolved
  split at resolved
  · rename_i record produced
    split at resolved
    · exact ⟨record,produced,by assumption,(Option.some.inj resolved).symm⟩
    · cases resolved
  · cases resolved

variable (record : Published model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law)

theorem the_received_occurrence_resolves_the_same_complete_choice :
    Publication.Plan.select model domain original reference worker receiver quote quotas slots point rival ordinal = some record.plan ∧
    (Segmented.trace model domain original reference worker quote quotas point rival).closingReceipt = some record.closing ∧
    Charge.paid quote model worker record.closing.before rival (Charge.endAt quote model worker record.closing.before rival) ∧
    record.receipt.statement.ballot.cut = record.closing.before.point.cut ∧ record.receipt.statement.ballot.key = worker ∧
    (Charge.fee quote)[record.receipt.statement.ballot.position]? = some record.receipt.statement.request ∧
    Prefix.Contract model domain original (reserved model original worker quote quotas) reference (.selected record.plan.choice) :=
  ⟨record.selected,record.sealed,record.closing.receipt,record.addressed.1,record.addressed.2.1,record.addressed.2.2,
    Publication.Plan.selected_full_contract model domain original reference worker receiver quote quotas slots point rival ordinal record.plan⟩

theorem every_published_address_has_real_paid_communication_and_local_readback :
    record.receipt.confirmation ∈ (observed model domain original reference worker receiver quote quotas slots point rival ordinal vocabulary encoding law record.plan).reception.receipts ∧
    record.receipt.statement ∈ RequestAttestation.ledger vocabulary point.point
      (stages model domain original reference worker receiver quote quotas slots point rival ordinal record.plan) ∧
    record.receipt.statement.ballot = record.receipt.confirmation.wire.ballot ∧
    RequestReadback.decode (code := model.source.code) record.receipt.confirmation.wire.signal = some record.receipt.statement.request ∧
    ∃ row, (StageTrace.records point.point (stages model domain original reference worker receiver quote quotas slots point rival ordinal record.plan))[record.receipt.confirmation.index]? = some row ∧
      record.receipt.reading = row.after.frame.inbox receiver ∧ model.source.code.memoryReady record.receipt.reading = true ∧
      RequestReadback.localRead (code := model.source.code) record.receipt.reading = some record.receipt.statement.request :=
  RequestReadback.recovered_requests_have_paid_communication_complete_source_and_local_readback vocabulary encoding law point.point
    (stages model domain original reference worker receiver quote quotas slots point rival ordinal record.plan) receiver _ record.receipt record.received

theorem the_publication_source_is_an_actual_prefix_of_the_full_selected_source :
    EventHistory.execute point.point (stages model domain original reference worker receiver quote quotas slots point rival ordinal record.plan) =
      Publication.Plan.cutPoint model domain original reference worker receiver quote quotas slots point rival ordinal record.plan.announcements.length := by
  have mapped (cursor : Cursor model.source.code) (controls : List (Prefix.Rule model.source.code)) :
      EventHistory.execute cursor (controls.map (fun rule => (rule,rival))) = Splice.install cursor rival controls := by
    induction controls generalizing cursor with
    | nil => rfl
    | cons head tail ih => exact ih (cursor.after head rival)
  rw [stages,mapped]
  have ready := Deployment.released_result_is_the_same_source_generated_cache model domain original reference worker quote quotas point rival ordinal
    record.plan.execution record.plan.finished record.plan.arrived
  obtain ⟨_,actual,_⟩ := Segmented.a_released_result_has_executed_the_entire_fixed_fee_plan
    model domain original reference worker quote quotas point rival record.plan.finished ready
  change Deployment.paidFinal model domain original reference worker quote quotas point rival = _ at actual
  calc
    _ = Splice.install (Deployment.paidFinal model domain original reference worker quote quotas point rival) rival record.plan.announcements := by
      rw [actual]
      unfold Splice.install
      rw [List.foldl_append]
      rfl
    _ = _ := (Publication.Installation.the_actual_communication_cut_is_the_paid_source_followed_by_the_registered_programme
      model domain original reference worker receiver quote quotas slots point rival ordinal record.plan record.selected).symm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Receipt
