import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateChecks

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveMandateSource ProductiveMandateChecks

def recoveredWork := (StageTrace.records start worked.stages).flatMap fun row =>
  ((Financial.inventoryAt (worked.current model start).source.input
    (ProgrammeHistory.visitAt (worked.current model start).source.input (EventStep.boundary row.cursor))).filterMap
      (Financial.InstructionOrigin.instruction? (worked.current model start).source.input)).map (fun item => item.request)

theorem the_original_financial_consumer_recovers_both_actual_productive_rounds :
    recoveredWork = body ++ body := by
  calc
    _ = (StageTrace.records start worked.stages).flatMap (fun row => row.submitted) := by
      apply List.flatMap_congr
      intro row inside
      exact (congrArg (List.map (fun item => item.request))
        (StageTrace.final_financial_inventory_is_the_original_record_items start worked.stages row inside)).trans
          (code.law.inventory_requests_exact row.before.current 0 row.submitted)
    _ = body ++ body := the_two_actual_owners_submit_and_pay_the_original_productive_word.1

theorem the_actual_productive_source_generates_a_service_receipt :
    ∃ receipt, service = .service receipt := by
  cases produced : service with
  | service receipt => exact ⟨receipt,rfl⟩
  | _ => have impossible := the_generated_material_funds_the_original_native_service
         simp only [serviceView,produced] at impossible
         cases impossible

theorem produced_material_closes_the_same_original_in_its_actual_root :
    ∃ receipt, service = .service receipt ∧
    let final := (NativeCommandCompiler.after model start worked receipt.ready).current model start
    let runtime := WithdrawalInquiryRuntime.runtime model final
    (∃ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
      HEq original receipt.original ∧ ∃ row ∈ (WithdrawalInquiryRuntime.authority model final).current.challenges,
        row.1 = original ∧ row.2.isPending (WithdrawalInquiryRuntime.family model final)
          (WithdrawalInquiryRuntime.sourceIndex model final) = false) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  obtain ⟨receipt,produced⟩ := the_actual_productive_source_generates_a_service_receipt
  have rooted := NativeCommandConsumer.the_actual_service_consumes_its_original_source_ledger_and_next model start worked receipt
  exact ⟨receipt,produced,NativeCommandConsumer.the_same_closed_original_is_in_the_actual_root_inventory model start worked receipt,
    rooted.2.2.2.2.2.1,rooted.2.2.2.2.2.2⟩

theorem actual_service_keeps_all_productive_requests_and_their_original_rows :
    ∃ receipt, service = .service receipt ∧
    (NativeCommandCompiler.after model start worked receipt.ready).inputs =
      inputs ++ [NativeCommandCompiler.input model start worked receipt.ready] ∧
    worked.entries <+: (NativeCommandCompiler.after model start worked receipt.ready).entries ∧
    (NativeCommandCompiler.after model start worked receipt.ready).entries.map (LocalCommandSource.Entry.row model) =
      StageTrace.records start (NativeCommandCompiler.after model start worked receipt.ready).stages := by
  obtain ⟨receipt,produced⟩ := the_actual_productive_source_generates_a_service_receipt
  have actual := NativeCommandConsumer.the_actual_service_consumes_its_original_source_ledger_and_next model start worked receipt
  have literal : worked.inputs = inputs := LocalCommandRun.the_source_keeps_every_input_in_order model start inputs
  exact ⟨receipt,produced,by rw [actual.1,literal],actual.2.1,actual.2.2.2.1⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateConsumer
