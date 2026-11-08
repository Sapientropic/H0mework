import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorConsumer

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev width := ForwardResponseClock.width model start

theorem the_generated_identity_window_is_consumed_by_the_original_root
    (past : JointResponse.Stages model) (delay : Nat) (positive : 0 < width model start)
    (reserve : SourceClockTermination.deadline model start past * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past)
    (available : ServiceActorWindow.Available model start vocabulary encoding law (SourceClockTermination.blocks model start past) past)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law (SourceClockTermination.deadline model start past) past).stages) :
    let full := (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    JointResponse.Clear model start vocabulary encoding law full ∧
    (∀ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
      row.2.isPending (WithdrawalInquiryRuntime.family model final) (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    past <+: full ∧
    StageAccountability.ledger start vocabulary encoding law past <+: StageAccountability.ledger start vocabulary encoding law full ∧
    (∀ receiver, (StageReception.run vocabulary encoding law start past receiver past.length).receipts <+:
      (StageReception.run vocabulary encoding law start full receiver full.length).receipts) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) :=
  SourceClockTermination.the_original_root_consumes_all_terminal_originals_ledger_and_own_next
    model start vocabulary encoding law past delay positive reserve
    (ServiceActorWindow.the_actual_identity_budget_generates_the_original_persistent_service_window
      model start vocabulary encoding law _ past available) compliant

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ServiceActorConsumer
