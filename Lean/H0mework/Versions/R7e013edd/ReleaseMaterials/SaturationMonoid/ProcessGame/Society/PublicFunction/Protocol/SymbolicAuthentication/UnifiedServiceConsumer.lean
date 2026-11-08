import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceConsumer
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

theorem the_actual_service_cut_retains_all_original_history_receipts_responsibilities_ledger_and_next
    (past : JointResponse.Stages model) (ready : UnifiedServiceSource.Ready model start vocabulary encoding law past) :
    let actual := ready.history
    let final := EventHistory.execute start actual
    let runtime := WithdrawalInquiryRuntime.runtime model final
    past <+: actual ∧ actual <+: UnifiedServiceSource.full model start vocabulary encoding law past ∧
    SignatureEligibility.Clear model start vocabulary encoding law actual ∧ 0 < JointResponse.fuel model start actual ∧
    StageAccountability.ledger start vocabulary encoding law past <+: StageAccountability.ledger start vocabulary encoding law actual ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start actual receiver actual.length).receipts) ∧
    (WithdrawalInquiryRuntime.authority model final).current =
      Native.Authority.fullGenerate (WithdrawalInquiryRuntime.native model final) (WithdrawalInquiryRuntime.depth model final) ∧
    (∀ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      let carried := Mandate.Challenge.through (WithdrawalInquiryRuntime.family model final)
        (WithdrawalInquiryRuntime.sourceIndex model final) original (WithdrawalInquiryRuntime.depth model final + 2)
      carried.state.current.history = carried.state.generated.events) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  have generated := UnifiedServiceSource.the_generated_cut_preserves_the_original_prefix_and_signature_journals
    model start vocabulary encoding law past ready
  obtain ⟨more, same⟩ := generated.1
  have ledger : StageAccountability.ledger start vocabulary encoding law past <+:
      StageAccountability.ledger start vocabulary encoding law ready.history := by
    rw [← same, StageAccountability.ledger_extends_by_its_generated_next]
    exact List.prefix_append _ _
  have receipts : ∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start ready.history receiver ready.history.length).receipts := by
    intro receiver
    rw [← same]
    exact StagePrefix.receipts_survive_actual_extension start past more vocabulary encoding law receiver
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (EventHistory.execute start ready.history)
  exact ⟨generated.1, generated.2.1, generated.2.2.1, generated.2.2.2.1,
    ledger, receipts, rooted.1, rooted.2.1, rooted.2.2.2.1, rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceConsumer
