import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDutyRuntime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDutyControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev foundation := StageQueueControls.foundation
abbrev start := StageQueueControls.start
abbrev pastStages := StageQueueControls.pastStages
abbrev protocols := StageQueueControls.protocols
abbrev vocabulary := StageQueueControls.vocabulary
abbrev encoding := StageQueueControls.encoding
abbrev law := StageQueueControls.law
abbrev slot := StageQueueControls.slot
abbrev full := StageQueueControls.full
abbrev origins (stages) := StageDuty.origins start vocabulary encoding stages
abbrev histories (stages) := StageDuty.histories start vocabulary encoding law stages
def tags (stages) := (histories stages).map fun row => row.2.2.state.slots.map fun
  | .live _ => false
  | .terminal _ => true

theorem actual_first_sends_generate_two_duties_and_retransmission_generates_no_new_admission :
    (StageTransport.wires vocabulary encoding start full).length = 3 ∧
      (origins full).map (fun emission => emission.wire) = [AdmissionControls.firstWire, AdmissionControls.secondWire] ∧
      (StageDuty.birth start vocabulary encoding full 10).isNone = true ∧
      tags full = [[true], [true]] := by
  decide +kernel

abbrev first := (StageDuty.birth start vocabulary encoding full 4).get (by decide +kernel)
abbrev suffix := full.drop first.birthStages.length
theorem the_admission_source_stops_at_the_original_send_and_is_preserved_under_extension :
    first.birthStages.length = 5 ∧ first.send = 4 ∧ first.wire = AdmissionControls.firstWire ∧
      (EventHistory.execute start first.birthStages).cut = 5 ∧
      (StageDuty.admission start vocabulary encoding law first).sourceEvent.emission.birthStages.length = 5 ∧
      StageDuty.birth start vocabulary encoding (full ++ full) 4 = StageDuty.birth start vocabulary encoding full 4 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact StageDuty.birth_survives_extension start vocabulary encoding full full 4 (by decide +kernel)

theorem the_original_obligation_closes_only_after_a_real_receipt :
    (StageDuty.through start vocabulary encoding law first []).2.state.LiveAt 0 ∧
      (StageDuty.through start vocabulary encoding law first suffix).2.state.TerminalAt 0 := by
  exact ⟨(StageDuty.live_iff_no_content_receipt start vocabulary encoding law first []).mpr (by decide +kernel),
    (StageDuty.terminal_iff_actual_content_receipt start vocabulary encoding law first suffix).mpr (by decide +kernel)⟩

theorem arbitrary_later_stages_retain_the_first_archive_and_its_complete_native_history
    (more : List (EventHistory.Stage (code := StageQueueControls.code))) :
    (StageDuty.through start vocabulary encoding law first (suffix ++ more)).2.state =
      (StageDuty.through start vocabulary encoding law first suffix).2.state :=
  StageDuty.first_archive_is_retained start vocabulary encoding law first suffix more
    the_original_obligation_closes_only_after_a_real_receipt.2

abbrev withheld := AdmissionControls.stages .withholdLast
theorem a_safe_decision_does_not_discharge_the_withheld_original_content :
    tags withheld = [[true], [true], [false]] ∧
      StageBudget.evidenceKeys vocabulary start withheld = {0} ∧
      AdmissionQuorum.produce AdmissionControls.base vocabulary encoding law start withheld 1 slot 2 = .decided true := by
  decide +kernel

theorem duplicate_receptions_do_not_allocate_or_discharge_an_unrelated_duty :
    tags StageQueueControls.resetStages = [[true], [false]] ∧
      (origins StageQueueControls.resetStages).length = 2 ∧
      StageDuty.birth start vocabulary encoding [] 4 = none ∧
      (StageDuty.origins start vocabulary StageQueueControls.forged full).isEmpty = true := by
  decide +kernel

abbrev stale := StageQueueControls.staleLaw
theorem expired_scope_and_missing_receipts_keep_the_original_registration_live :
    (StageDuty.through start vocabulary encoding stale first suffix).2.state.LiveAt 0 ∧
      (StageDuty.through start vocabulary encoding StageQueueControls.lateLaw first suffix).2.state.LiveAt 0 ∧
      (StageDuty.origins start vocabulary encoding (full.take 4)).isEmpty = true := by
  exact ⟨(StageDuty.live_iff_no_content_receipt start vocabulary encoding stale first suffix).mpr (by decide +kernel),
    (StageDuty.live_iff_no_content_receipt start vocabulary encoding StageQueueControls.lateLaw first suffix).mpr (by decide +kernel),
    by decide +kernel⟩

abbrev poorFirst := (StageDuty.birth StageQueueControls.poorStart vocabulary StageQueueControls.poorEncoding
  StageQueueControls.poorFull 4).get (by decide +kernel)
theorem an_unpaid_actual_delivery_keeps_the_first_paid_send_live :
    (StageDuty.through StageQueueControls.poorStart vocabulary StageQueueControls.poorEncoding StageQueueControls.poorLaw
      poorFirst (StageQueueControls.poorFull.drop poorFirst.birthStages.length)).2.state.LiveAt 0 := by
  apply (StageDuty.live_iff_no_content_receipt _ _ _ _ _ _).mpr
  decide +kernel

abbrev rooted := StageDutyRuntime.rooted foundation start pastStages protocols vocabulary encoding law slot 2
abbrev runtime := StageDutyRuntime.activated foundation start pastStages protocols vocabulary encoding law slot 2
  (StageDutyRuntime.ordinal foundation start pastStages protocols)

theorem the_independent_root_consumer_uses_the_original_duty_receipt_ledger_and_next :
    ∃ row ∈ rooted.duties, row.1.wire = AdmissionControls.firstWire ∧ row.2.2.state.TerminalAt 0 ∧
      (rooted.source.source.decisions 1 = .decided true) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law slot 2).process.stateAt
        ((StageDutyRuntime.facade foundation start pastStages protocols vocabulary encoding law slot 2).process.successor runtime.state) := by
  have projected : rooted.duties.map (fun row => row.1.wire) = [AdmissionControls.firstWire, AdmissionControls.secondWire] := by
    change ((origins full).map (fun emission => (⟨emission, StageDuty.through start vocabulary encoding law emission
      (full.drop emission.birthStages.length)⟩ : Sigma (StageDuty.History start vocabulary encoding law)))).map _ = _
    simpa only [List.map_map, Function.comp_def] using actual_first_sends_generate_two_duties_and_retransmission_generates_no_new_admission.2.1
  have present : AdmissionControls.firstWire ∈ rooted.duties.map (fun row => row.1.wire) := by rw [projected]; simp
  obtain ⟨row, inside, same⟩ := List.mem_map.mp present
  have consumed := StageDutyRuntime.rooted_duty_consumes_original_identity_receipt_whole_ledger_and_next
    foundation start pastStages protocols vocabulary encoding law slot 2 row inside
  have recipient : row.1.wire.recipient = 1 := by rw [same]
  have ready : StageQueueProgress.readyAt vocabulary encoding law start full row.1.wire.recipient 5 =
      some AdmissionControls.firstWire := by
    rw [recipient]
    decide +kernel
  have finished := StageDuty.generated_ready_delivery_settles_the_original_native_duty start vocabulary encoding law full row inside
    5 AdmissionControls.firstWire (by decide +kernel) ready
    (congrArg (fun wire : StageTransport.Wire (code := StageQueueControls.code) => wire.ballot) same.symm)
  exact ⟨row, inside, same, finished, by decide +kernel,
    consumed.2.2.2.2.2.2.1, consumed.2.2.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDutyControls
