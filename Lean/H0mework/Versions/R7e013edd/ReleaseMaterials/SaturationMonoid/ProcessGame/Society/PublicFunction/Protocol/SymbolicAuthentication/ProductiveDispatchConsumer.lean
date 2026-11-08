import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchChecks

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveDispatchSource ProductiveDispatchTrace ProductiveDispatchChecks

theorem every_joint_receipt_recovers_its_actual_owned_paid_request
    (receiver : Fin model.source.code.sites) (receipt : StageReception.Receipt (code := model.source.code))
    (inside : receipt ∈ (observed actual receiver).receipts) :
    ∃ row ∈ StageTrace.records start actual.stages, ∃ (position : Nat)
      (item : ExecutionItem Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit),
      (StageTrace.items row)[position]? = some item ∧ model.source.code.law.Valid item.before item.request ∧
      item.request.signer = model.source.code.siteParty receipt.wire.ballot.key ∧
      0 < receipt.wire.ballot.fee := by
  have origin := HeaderReception.receipt_has_original_paid_ballot vocabulary law start actual.stages receiver actual.stages.length receipt inside
  obtain ⟨row,member,position,made⟩ := StageBudget.ledger_origin vocabulary start actual.stages receipt.wire.ballot origin
  obtain ⟨site,item,_,present,paid,signed,_,_,key,_,_,_,fee⟩ := StageBudget.issued_has_an_owned_valid_paid_origin vocabulary row position receipt.wire.ballot made
  refine ⟨row,member,position,item,present,paid,?_,fee⟩
  change item.request.signer = ProductiveHeaderSource.old.siteParty receipt.wire.ballot.key
  exact signed.trans (congrArg ProductiveHeaderSource.old.siteParty key.symm)

theorem the_joint_execution_retains_all_original_financial_accounts
    (ordinal : Nat) (earlier : ordinal ≤ EventStep.boundary ProductiveHeaderSource.saved) :
    Native.Coupling.Match ProductiveHeaderSource.old ProductiveHeaderSource.saved.source.input
      (actual.current model start).source.input
      (Financial.accountAt ProductiveHeaderSource.saved.source.input ordinal)
      (Financial.accountAt (actual.current model start).source.input ordinal) :=
  CatalogueHandoffSource.completeFinancialPrefix ProductiveHeaderSource.old ProductiveHeaderSource.catalogue
    ProductiveHeaderSource.saved (by rfl) actual.stages ordinal earlier

theorem every_actual_productive_request_is_in_the_final_native_inventory
    (row : StageTrace.Record (code := model.source.code)) (inside : row ∈ StageTrace.records start actual.stages) :
    ((Financial.inventoryAt (actual.current model start).source.input
      (ProgrammeHistory.visitAt (actual.current model start).source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (actual.current model start).source.input)) = StageTrace.items row :=
  StageTrace.final_financial_inventory_is_the_original_record_items start actual.stages row inside

theorem actual_joint_production_and_quorums_keep_the_native_whole_ledger_and_generated_next :
    let final := actual.current model start
    let runtime := WithdrawalInquiryRuntime.runtime model final
    decideAt actual zero = .decided true ∧ decideAt actual one = .decided true ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    (actual.current model start)
  exact ⟨the_same_actual_production_funds_both_identity_quorums.2.2.2.2.2.2.1,
    the_same_actual_production_funds_both_identity_quorums.2.2.2.2.2.2.2,rooted.2.2.2.1,rooted.2.2.2.2⟩

theorem every_generated_prefix_keeps_the_original_fuel_bound (count : Nat) :
    (EventStep.seed ((journey initial count).1.current model start)).remaining = 23-count := by
  rw [every_generated_prefix_spends_its_original_invocation_account,
    the_original_native_service_endpoint_funds_twenty_three_invocations]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveDispatchConsumer
