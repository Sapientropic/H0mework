import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Production
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation
open Institutions.Capitalism.Universal.Source.Program
abbrev PublicRule := @Distributed.Recall.Information.Agency.Protocol.Rule
abbrev PublicProgram := @Distributed.Recall.Information.Agency.Protocol.Continuation.Whole.Program
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (budget : Nat) (published : List (PublicRule seed.source.code))
  {fuel : Nat} (original : PublicRule seed.source.code)
  (reference : PublicProgram seed.source.code fuel) (fallback : PublicRule seed.source.code)

/-- Public preparation has no actual cursor, receipt signal, chosen policy or coverage input. -/
structure Prepared where
  private mk ::
  controller : PublicRule seed.source.code
  generated : controller = Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.rule seed
    (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript.views seed budget published) original reference fallback

def prepare : Prepared seed budget published original reference fallback :=
  ⟨Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.rule seed (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript.views seed budget published)
    original reference fallback,rfl⟩

variable {seed budget published original reference fallback}
  (prepared : Prepared seed budget published original reference fallback)
  {driver : Feedback.Input seed.source.code}

def signal (point : Cursor seed driver) (site : Fin seed.source.code.sites) : Fin seed.source.code.signals :=
  (point.same_code ▸ point.state : Feedback.State seed.source.code).frame.inbox site

namespace Prepared

def requested (point : Cursor seed driver) (site : Fin seed.source.code.sites) :
    List (Future.Recovery.Action point.model) :=
  prepared.controller.work.val (site,signal point site) (seed.source.code.key_mem _)

def event (point : Cursor seed driver) (site : Fin seed.source.code.sites) :=
  Distributed.Recall.Information.Agency.Protocol.localEvent seed.source.code prepared.controller site (signal point site)

theorem requested_is_the_original_registered_local_head
    (point : Cursor seed driver) (site : Fin seed.source.code.sites) :
    prepared.requested point site =
      (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.head seed (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript.views seed budget published)
        original reference fallback site (signal point site)).work.val
          (site,signal point site) (seed.source.code.key_mem _) := by
  unfold requested
  rw [prepared.generated]
  exact Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Rolling.Receipt.the_actual_work_reads_the_same_receipt_selected_plan _ _ _ _ _ _ _

theorem requested_is_bounded_by_the_original_source_menu
    (point : Cursor seed driver) (site : Fin seed.source.code.sites) :
    prepared.requested point site ∈ words point.source.val.code.actions point.source.val.code.actionLimit := by
  rw [point.same_code]
  exact (List.mem_pi _ _).mp prepared.controller.work.property _ (seed.source.code.key_mem _)

theorem indistinguishable_local_records_generate_the_same_request
    {otherDriver : Feedback.Input seed.source.code}
    (first : Cursor seed driver) (second : Cursor seed otherDriver)
    (site : Fin seed.source.code.sites) (same : signal first site = signal second site) :
    prepared.requested first site = prepared.requested second site := by
  exact congrArg (fun reading => prepared.controller.work.val (site,reading) (seed.source.code.key_mem _)) same

variable {cursor : Cursor seed driver}
  {pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)}
  {n : Nat} {nativeReference : Term cursor} {actor : Party} {position : Nat}
  (scope : Scope cursor pricing n nativeReference actor position)

def receive (site : Fin seed.source.code.sites) :=
  Production.fromRequested scope (prepared.requested (comparisonPoint scope) site)

theorem a_received_head_is_issued_exactly_when_it_is_personally_authorized
    (site : Fin seed.source.code.sites) :
    (prepared.receive scope site).isSome = true ↔
      Mandate.Replay.Personal actor (prepared.requested (comparisonPoint scope) site) := by
  rw [receive,Production.fromRequested_is_some_exactly_for_registered_personal_words,
    Prefix.own_words_are_exactly_bounded_personal_requests]
  exact ⟨And.right,fun personal => ⟨prepared.requested_is_bounded_by_the_original_source_menu _ _,personal⟩⟩

/-- Only the raw work head is issued here; the saved event remains available to its original driver. -/
def run (site : Fin seed.source.code.sites) (span : Nat) :
    Option (Reservation.Protocol cursor pricing n nativeReference actor position span) :=
  (prepared.receive scope site).map fun issued => issued.val.run span

theorem every_issued_head_reaches_the_original_paid_consumer
    (site : Fin seed.source.code.sites) (span : Nat)
    (issued : {candidate : Production.Candidate scope //
      candidate.own.requested = prepared.requested (comparisonPoint scope) site})
    (generated : prepared.receive scope site = some issued) :
    prepared.run scope site span = some (issued.val.run span) ∧
    ((comparisonPoint issued.val.source).source.val.actualExecution (comparisonPoint scope).depth).submitted =
      issued.val.own.execution.output ∧
    issued.val.own.execution.consumed ++ issued.val.own.execution.residual =
      prepared.requested (comparisonPoint scope) site ∧
    (issued.val.read span).execution.origin = some issued.val.source ∧
    (issued.val.read span).learning = (issued.val.run span).endpoint ∧
    HEq ((Reservation.Runtime.facade (issued.val.run span)).readoutAt
      (Reservation.Runtime.activated (issued.val.run span)) .computation)
      ((Reservation.Runtime.activated (issued.val.run span)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (Reservation.Runtime.activated (issued.val.run span)).tick.generated.wholeLedgerWriteBack
      ((Reservation.Runtime.activated (issued.val.run span)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Reservation.Runtime.activated (issued.val.run span)).current.visit.current) ∧
    (Reservation.Runtime.activated (issued.val.run span)).tick.nextCurrent =
      (Reservation.Runtime.process (issued.val.run span)).stateAt
        ((Reservation.Runtime.process (issued.val.run span)).successor
          (Reservation.Runtime.activated (issued.val.run span)).state) := by
  have native := issued.val.the_original_root_retains_the_generated_action_source_and_whole_window span
  have rooted := issued.val.the_same_original_root_consumes_the_action_reservation_and_own_next span
  refine ⟨?_,issued.val.action_is_the_exact_last_actual_source_event,
    issued.val.action_preserves_the_original_requests_and_exact_residual.trans issued.property,
    native.1,native.2.1,rooted.2.2.1,rooted.2.2.2.1,rooted.2.2.2.2⟩
  simp only [run,generated,Option.map_some]

end Prepared
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation
