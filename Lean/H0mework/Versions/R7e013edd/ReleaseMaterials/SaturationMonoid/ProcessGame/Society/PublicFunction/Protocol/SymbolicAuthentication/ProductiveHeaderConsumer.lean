import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderChecks

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ProductiveHeaderSource ProductiveHeaderChecks

theorem the_original_financial_prefix_survives_the_entire_broadcast
    (ordinal : Nat) (earlier : ordinal ≤ EventStep.boundary saved) :
    Native.Coupling.Match old saved.source.input (actual.current model start).source.input
      (Financial.accountAt saved.source.input ordinal)
      (Financial.accountAt (actual.current model start).source.input ordinal) :=
  CatalogueHandoffSource.completeFinancialPrefix old catalogue saved (by rfl) actual.stages ordinal earlier

theorem every_actual_header_receipt_recovers_its_original_paid_request
    (receiver : Fin code.sites) (receipt : StageReception.Receipt (code := code))
    (inside : receipt ∈ (observed receiver).receipts) :
    ∃ row ∈ StageTrace.records start actual.stages, ∃ (position : Nat)
      (item : ExecutionItem Bool Bool ProductiveMandateSource.Port (Mandate.State Bool Bool) Unit),
      (StageTrace.items row)[position]? = some item ∧ code.law.Valid item.before item.request ∧
      item.request.signer = code.siteParty receipt.wire.ballot.key ∧
      0 < receipt.wire.ballot.fee := by
  have origin := HeaderReception.receipt_has_original_paid_ballot vocabulary law start actual.stages receiver actual.stages.length receipt inside
  obtain ⟨row,member,position,made⟩ := StageBudget.ledger_origin vocabulary start actual.stages receipt.wire.ballot origin
  obtain ⟨site,item,_,present,paid,signed,_,_,key,_,_,_,fee⟩ := StageBudget.issued_has_an_owned_valid_paid_origin vocabulary row position receipt.wire.ballot made
  exact ⟨row,member,position,item,present,paid,by simpa only [key] using signed,fee⟩

theorem each_original_row_is_in_the_actual_final_financial_inventory
    (row : StageTrace.Record (code := code)) (inside : row ∈ StageTrace.records start actual.stages) :
    ((Financial.inventoryAt (actual.current model start).source.input
      (ProgrammeHistory.visitAt (actual.current model start).source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? (actual.current model start).source.input)) = StageTrace.items row :=
  StageTrace.final_financial_inventory_is_the_original_record_items start actual.stages row inside

theorem actual_header_decisions_agree_under_their_generated_source_budget
    (leftLaw rightLaw : StageReception.Law code) (left right : Fin code.sites) (threshold : Nat) (a b : Bool)
    (one : HeaderQuorum.produce start vocabulary leftLaw actual.stages left scope threshold = .decided a)
    (two : HeaderQuorum.produce start vocabulary rightLaw actual.stages right scope threshold = .decided b) : a = b :=
  HeaderQuorum.produced_decisions_agree start vocabulary leftLaw rightLaw actual.stages left right scope threshold a b one two

theorem actual_broadcast_and_the_same_native_root_keep_whole_ledger_and_next :
    let final := actual.current model start
    let runtime := WithdrawalInquiryRuntime.runtime model final
    decideAt zero = .decided true ∧ decideAt one = .decided true ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
      ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    (actual.current model start)
  exact ⟨both_actual_receivers_generate_distinct_identity_quorums.2.2.2.2.2.1,
    both_actual_receivers_generate_distinct_identity_quorums.2.2.2.2.2.2,rooted.2.2.2.1,rooted.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveHeaderConsumer
