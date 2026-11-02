import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedRetry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedRetryRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (past : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (protocols : Nat → Rule (AdmissionRuntime.profile foundation).source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)

abbrev emitted := TimedRetry.stages start past vocabulary encoding law
abbrev queueSuffix := StageQueue.stages (EventHistory.execute start (emitted foundation start past vocabulary encoding law))
  protocols (StageQueue.horizon (EventHistory.execute start (emitted foundation start past vocabulary encoding law)))
abbrev full := StageQueueProgress.completeStages start (emitted foundation start past vocabulary encoding law) protocols
abbrev rooted := StageAccountabilityRuntime.rooted foundation start (emitted foundation start past vocabulary encoding law)
  protocols vocabulary encoding law scope threshold
abbrev runtime := StageAccountabilityRuntime.activated foundation start (emitted foundation start past vocabulary encoding law)
  protocols vocabulary encoding law scope threshold
  (StageAccountabilityRuntime.ordinal foundation start (emitted foundation start past vocabulary encoding law) protocols)
abbrev facade := StageAccountabilityRuntime.facade foundation start (emitted foundation start past vocabulary encoding law)
  protocols vocabulary encoding law scope threshold

variable (answer : TimedRetry.Ready start past vocabulary encoding law)
  (selected : TimedRetry.produce start past vocabulary encoding law = .ready answer)

def originalRow : Sigma (StageDuty.History start vocabulary encoding law) :=
  ⟨answer.overdue.emission, StageDuty.through start vocabulary encoding law answer.overdue.emission
    ((full foundation start past protocols vocabulary encoding law).drop answer.overdue.emission.birthStages.length)⟩

include selected in
theorem original_duty_is_in_the_same_root :
    originalRow foundation start past protocols vocabulary encoding law answer ∈
      (rooted foundation start past protocols vocabulary encoding law scope threshold).source.duties := by
  have chosen : emitted foundation start past vocabulary encoding law = answer.stages :=
    TimedRetry.ready_appends_the_generated_schedule start past vocabulary encoding law answer selected
  obtain ⟨more, extension⟩ := TimedRetry.the_original_history_is_preserved start past vocabulary encoding law answer
  have original := TimedDuty.original_emission_survives_extension start past vocabulary encoding law answer.overdue
    (more ++ queueSuffix foundation start past protocols vocabulary encoding law)
  have actual : answer.overdue.emission ∈ StageDuty.origins start vocabulary encoding
      (full foundation start past protocols vocabulary encoding law) := by
    change answer.overdue.emission ∈ StageDuty.origins start vocabulary encoding
      (emitted foundation start past vocabulary encoding law ++ queueSuffix foundation start past protocols vocabulary encoding law)
    rw [chosen, ← extension, List.append_assoc]
    exact original
  exact List.mem_map.mpr ⟨answer.overdue.emission, actual, rfl⟩

include selected in
theorem actual_retry_receipt_is_retained_in_the_same_root :
    ∃ receipt ∈ ((rooted foundation start past protocols vocabulary encoding law scope threshold).source.source.source.receivers
      answer.overdue.emission.wire.recipient).receipts,
      receipt.wire.ballot = answer.overdue.emission.wire.ballot := by
  obtain ⟨row, inside, identity, terminal⟩ :=
    TimedRetry.new_actual_delivery_terminates_the_original_duty start past vocabulary encoding law answer
  obtain ⟨receipt, received, body⟩ :=
    (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law answer.stages row inside).mp terminal
  have recipient := congrArg (fun emission => emission.wire.recipient) identity
  have ballot := congrArg (fun emission => emission.wire.ballot) identity
  have retained := (StagePrefix.receipts_survive_actual_extension start answer.stages
    (queueSuffix foundation start past protocols vocabulary encoding law) vocabulary encoding law row.1.wire.recipient).subset received
  rw [recipient] at retained
  refine ⟨receipt, ?_, body.trans ballot⟩
  change receipt ∈ (StageReception.run vocabulary encoding law start
    (TimedRetry.stages start past vocabulary encoding law ++ queueSuffix foundation start past protocols vocabulary encoding law)
    answer.overdue.emission.wire.recipient
    (TimedRetry.stages start past vocabulary encoding law ++ queueSuffix foundation start past protocols vocabulary encoding law).length).receipts
  rw [TimedRetry.ready_appends_the_generated_schedule start past vocabulary encoding law answer selected]
  exact retained

include selected in
theorem repaired_original_duty_consumes_receipt_history_whole_ledger_and_next :
    let state := runtime foundation start past protocols vocabulary encoding law scope threshold
    let row := originalRow foundation start past protocols vocabulary encoding law answer
    row.2.2.state.TerminalAt 0 ∧
      (∀ archive, row.2.2.state.slots[0]? = some (.terminal archive) →
        archive.obligation = StageDuty.obligation start vocabulary encoding law answer.overdue.emission) ∧
      answer.overdue.emission.birthStages ++ row.2.1 = full foundation start past protocols vocabulary encoding law ∧
      HEq ((facade foundation start past protocols vocabulary encoding law scope threshold).readoutAt state (.previous .duties))
        (state.tick.generated.projectionOutcome (.inherited (.component ()))) ∧
      HEq ((facade foundation start past protocols vocabulary encoding law scope threshold).readoutAt state .accountability)
        (state.tick.generated.projectionOutcome (.component ())) ∧
      HEq state.tick.generated.wholeLedgerWriteBack
        (state.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt state.current.visit.current) ∧
      state.tick.nextCurrent = (facade foundation start past protocols vocabulary encoding law scope threshold).process.stateAt
        ((facade foundation start past protocols vocabulary encoding law scope threshold).process.successor state.state) := by
  have inside := original_duty_is_in_the_same_root foundation start past protocols vocabulary encoding law scope threshold answer selected
  have receipt := actual_retry_receipt_is_retained_in_the_same_root foundation start past protocols vocabulary encoding law scope threshold answer selected
  have actual : originalRow foundation start past protocols vocabulary encoding law answer ∈
      StageDuty.histories start vocabulary encoding law (full foundation start past protocols vocabulary encoding law) := inside
  have terminal := (StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law _ _ actual).mpr receipt
  have original := StageDuty.original_admission_and_complete_native_history start vocabulary encoding law answer.overdue.emission
    ((full foundation start past protocols vocabulary encoding law).drop answer.overdue.emission.birthStages.length)
  have duty := (facade foundation start past protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start past protocols vocabulary encoding law scope threshold) (.previous .duties)
  have evidence := (facade foundation start past protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start past protocols vocabulary encoding law scope threshold) .accountability
  exact ⟨terminal, original.2.2,
    StageDuty.generated_row_observes_the_original_whole_history start vocabulary encoding law _ _ actual,
    duty.2.2.2.1, evidence.2.2.2.1, evidence.2.2.1, evidence.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.TimedRetryRuntime
