import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalWindowRun

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshReception
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code)

abbrev Mailbox := Fin code.sites → List (RequestReadback.Receipt (code := code))

-- Only delivery at the just executed stage enters the local continuation.
def poll (past : List (EventHistory.Stage (code := code))) (site : Fin code.sites) :=
  (RequestReadback.produce vocabulary encoding law start past site past.length).receipts.filter
    fun receipt => decide (receipt.confirmation.index + 1 = past.length)

private theorem record_after_is_the_exact_prefix
    (past : List (EventHistory.Stage (code := code))) (index : Nat)
    (row : StageTrace.Record (code := code)) (found : (StageTrace.records start past)[index]? = some row) :
    row.after = EventStep.seed (EventHistory.execute start (past.take (index + 1))) := by
  induction past generalizing start index with
  | nil => simp only [StageTrace.records, List.getElem?_nil] at found; cases found
  | cons stage rest ih =>
    rcases stage with ⟨rule, rival⟩
    cases index with
    | zero =>
      simp only [StageTrace.records, List.getElem?_cons_zero] at found
      cases Option.some.inj found
      exact (StageTrace.material_is_the_actual_step start rule rival).1
    | succ index =>
      simp only [StageTrace.records, List.getElem?_cons_succ] at found
      simpa only [List.take_succ_cons, EventHistory.execute] using ih (start.after rule rival) index found

theorem every_fresh_receipt_is_paid_and_reads_this_actual_cut
    (past : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (receipt : RequestReadback.Receipt (code := code))
    (inside : receipt ∈ poll vocabulary encoding law start past site) :
    receipt ∈ (RequestReadback.produce vocabulary encoding law start past site past.length).receipts ∧
      receipt.confirmation.index + 1 = past.length ∧
      receipt.statement ∈ RequestAttestation.ledger vocabulary start past ∧
      receipt.reading = (EventStep.seed (EventHistory.execute start past)).frame.inbox site ∧
      RequestReadback.localRead (code := code) receipt.reading = some receipt.statement.request := by
  obtain ⟨paid, edge⟩ := List.mem_filter.mp inside
  have latest := of_decide_eq_true edge
  obtain ⟨_, source, _, _, row, found, reading, _, decoded⟩ :=
    RequestReadback.recovered_requests_have_paid_communication_complete_source_and_local_readback
      vocabulary encoding law start past site past.length receipt paid
  have actual := record_after_is_the_exact_prefix start past receipt.confirmation.index row found
  rw [latest, List.take_length] at actual
  exact ⟨paid, latest, source, reading.trans (congrArg (fun state : State code => state.frame.inbox site) actual), decoded⟩

theorem different_stage_polls_cannot_reuse_a_receipt
    (first second : List (EventHistory.Stage (code := code))) (site : Fin code.sites)
    (different : first.length ≠ second.length) (receipt : RequestReadback.Receipt (code := code))
    (inside : receipt ∈ poll vocabulary encoding law start first site) :
    receipt ∉ poll vocabulary encoding law start second site := by
  intro repeated
  have a := (every_fresh_receipt_is_paid_and_reads_this_actual_cut vocabulary encoding law start first site receipt inside).2.1
  have b := (every_fresh_receipt_is_paid_and_reads_this_actual_cut vocabulary encoding law start second site receipt repeated).2.1
  exact different (a.symm.trans b)

def queue (pending incoming : Mailbox (code := code)) : Mailbox (code := code) :=
  fun site => pending site ++ incoming site

def Accounted (past : List (EventHistory.Stage (code := code))) (pending : Mailbox (code := code)) : Prop :=
  ∀ site receipt, receipt ∈ pending site → ∃ entry, entry <+: past ∧
    receipt ∈ (RequestReadback.produce vocabulary encoding law start entry site entry.length).receipts

theorem queue_keeps_every_receipts_own_actual_source
    (past : List (EventHistory.Stage (code := code))) (pending : Mailbox (code := code))
    (paid : Accounted vocabulary encoding law start past pending) :
    Accounted vocabulary encoding law start past (queue pending (poll vocabulary encoding law start past)) := by
  intro site receipt inside
  rcases List.mem_append.mp inside with old | fresh
  · exact paid site receipt old
  · exact ⟨past, List.prefix_refl _,
      (every_fresh_receipt_is_paid_and_reads_this_actual_cut vocabulary encoding law start past site receipt fresh).1⟩

theorem accountable_pending_survives_actual_extension
    (past more : List (EventHistory.Stage (code := code))) (pending : Mailbox (code := code))
    (paid : Accounted vocabulary encoding law start past pending) :
    Accounted vocabulary encoding law start (past ++ more) pending := by
  intro site receipt inside
  obtain ⟨entry, kept, source⟩ := paid site receipt inside
  exact ⟨entry, kept.trans (List.prefix_append _ _), source⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshReception
