import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityServiceTrace

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityServiceConsumer
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (rounds : Nat) (past : JointResponse.Stages model)
  (ready : PriorityServiceTrace.Ready model start vocabulary encoding law rounds past)

theorem the_generated_service_window_has_actual_room_and_original_journal_progress :
    let full := (JointResponseRun.run model start vocabulary encoding law rounds past).stages
    let width := ready.index + 1 - past.length
    past.length ≤ ready.index ∧ ready.index < past.length + width ∧
    past.length + width ≤ full.length ∧
    RejectionService.ServedAt model start vocabulary encoding law full ready.index ∧
    RejectionProgress.count model start vocabulary encoding law (full.take (ready.index + 1)) =
      RejectionProgress.count model start vocabulary encoding law (full.take ready.index) + 1 := by
  dsimp only
  have served := PriorityServiceTrace.the_first_source_selected_service_is_an_actual_row
    model start vocabulary encoding law rounds past ready.index ready.selected
  exact ⟨served.1, by omega, by omega, served.2.2,
    RejectionService.actual_service_registers_one_new_response model start vocabulary encoding law _ _ served.2.2⟩

theorem the_original_root_consumes_the_generated_service_without_erasing_native_responsibilities :
    let full := (JointResponseRun.run model start vocabulary encoding law rounds past).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    past <+: full ∧
    RejectionService.ServedAt model start vocabulary encoding law full ready.index ∧
    (∀ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      let history := Mandate.Challenge.through (WithdrawalInquiryRuntime.family model final)
        (WithdrawalInquiryRuntime.sourceIndex model final) original (WithdrawalInquiryRuntime.depth model final + 2)
      history.state.current.history = history.state.generated.events) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have served := PriorityServiceTrace.the_first_source_selected_service_is_an_actual_row
    model start vocabulary encoding law rounds past ready.index ready.selected
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (EventHistory.execute start (JointResponseRun.run model start vocabulary encoding law rounds past).stages)
  exact ⟨JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law rounds past,
    served.2.2, rooted.2.1, rooted.2.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityServiceConsumer
