import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowChecks
set_option autoImplicit false
set_option maxRecDepth 100000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open DispatchWindowSource DispatchWindowChecks

theorem the_new_window_keeps_the_original_debt_and_the_actual_paid_stock :
 (EventStep.seed point).current.stock false true = 7 ∧
 (EventStep.seed point).current.stock true true = 1 ∧
 (EventStep.seed point).current.claims () false true = 7 ∧
 (EventStep.seed point).current.technology.holder = none := by
 rw [PaidInvocationSource.paid_opening_preserves_the_entire_actual_endpoint old contract saved true true actualAdmission]
 exact ⟨the_original_successor_pays_the_provider_and_obtains_actual_acceptance.2.1,
  the_original_successor_pays_the_provider_and_obtains_actual_acceptance.2.2.1,
  the_original_successor_pays_the_provider_and_obtains_actual_acceptance.2.2.2.1,
  the_original_successor_pays_the_provider_and_obtains_actual_acceptance.2.2.2.2.1⟩

theorem the_provider_was_actually_credited_the_original_payment_unit :
 old.law.Valid row.before.current payment ∧
 flowAt (old.law.actualDebit row.before.current payment) true true = 1 ∧
 flowAt (old.law.actualCredit row.before.current payment) false true = 1 := by
 have source := PaidInvocationSource.actual_admission_requires_both_original_valid_occurrences old contract saved true true actualAdmission
 have item : ⟨0,row.before.current,payment⟩ ∈ StageTrace.items row := by
  rw [StageTrace.items]
  rw [source.1]
  simp only [RawLaw.rawItems,RawLaw.execute,List.mem_cons,List.not_mem_nil,or_false]
  rfl
 exact ⟨source.2.2.2.2.1 _ item,source.2.2.2.2.2.2.2.2.1,source.2.2.2.2.2.2.2.2.2.1⟩

theorem every_paid_history_row_is_recoverable_from_the_new_native_inventory
 (record : StageTrace.Record (code := code)) (inside : record ∈ StageTrace.records start (PaidInvocationSource.stages old contract true true)) :
 ((Financial.inventoryAt paid.source.input
   (ProgrammeHistory.visitAt paid.source.input (EventStep.boundary record.cursor))).filterMap
   (Financial.InstructionOrigin.instruction? paid.source.input)) = StageTrace.items record :=
 StageTrace.final_financial_inventory_is_the_original_record_items start (PaidInvocationSource.stages old contract true true) record inside

theorem all_paid_financial_accounts_survive_the_opening (ordinal : Nat) (earlier : ordinal ≤ EventStep.boundary paid) :
 Native.Coupling.Match code paid.source.input point.source.input
 (Financial.accountAt paid.source.input ordinal) (Financial.accountAt point.source.input ordinal) :=
 PaidInvocationSource.paid_opening_preserves_every_original_financial_account old contract saved true true actualAdmission ordinal earlier

theorem every_original_account_survives_payment_acceptance_and_window_opening
 (ordinal : Nat) (earlier : ordinal ≤ EventStep.boundary saved) :
 Native.Coupling.Match old saved.source.input point.source.input
 (Financial.accountAt saved.source.input ordinal) (Financial.accountAt point.source.input ordinal) := by
 have prior := CatalogueHandoffSource.completeFinancialPrefix old (PaidInvocationSource.catalogue old contract)
  saved (by rfl) (PaidInvocationSource.stages old contract true true) ordinal earlier
 have bound : EventStep.boundary saved ≤ EventStep.boundary paid := by
  change saved.history.length+2+saved.cut ≤ saved.history.length+2+(saved.cut+1+1)
  omega
 have within := (PaidInvocationSource.actual_admission_requires_both_original_valid_occurrences
  old contract saved true true actualAdmission).2.2.2.2.2.2.2.2.2.2
 have next := Native.Coupling.History.complete_accounts old paid.source.input point.source.input rfl rfl
  (EventStep.boundary paid) (PaidInvocationRebase.prior_raw_event paid contract.steps within)
  paid.source.body point.source.body rfl rfl ordinal (earlier.trans bound)
 exact ⟨next.slots.trans prior.slots,next.events.trans prior.events⟩

def reception : StageReception.Law code := ⟨fun _ _ => ProductiveDispatchSource.scope,1⟩
def state := LocalCommandRun.initial (model point) point

theorem the_paid_window_is_consumed_by_the_original_dynamic_dispatch (count : Nat) (within : count ≤ 36) :
 HeaderDispatch.actual (model point) point ProductiveDispatchSource.vocabulary reception 0 state count =
 .running (HeaderDispatch.journey (model point) point ProductiveDispatchSource.vocabulary reception 0 state count).1 :=
 HeaderDispatch.original_fuel_generates_every_actual_admitted_dispatch_prefix
 (model point) point ProductiveDispatchSource.vocabulary reception 0 state count
 (by change count ≤ (EventStep.seed point).remaining;rw [the_paid_window_has_thirty_six_new_invocations];exact within)

theorem the_actual_new_source_keeps_its_whole_ledger_and_own_generated_next :
 let runtime := WithdrawalInquiryRuntime.runtime (model point) point
 HEq runtime.tick.generated.wholeLedgerWriteBack
 (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
 runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade (model point) point).process.stateAt
 ((WithdrawalInquiryRuntime.facade (model point) point).process.successor runtime.state) :=
 (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next (model point) point).2.2.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchWindowConsumer
