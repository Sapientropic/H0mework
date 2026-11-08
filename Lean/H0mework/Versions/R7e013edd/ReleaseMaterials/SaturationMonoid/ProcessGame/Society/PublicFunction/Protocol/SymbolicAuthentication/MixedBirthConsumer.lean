import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthBudget
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
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

theorem the_same_original_root_consumes_the_finite_mixed_budget_and_its_own_next
    (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.produce model start vocabulary encoding law past).stages) :
    let rounds := JointResponse.fuel model start past
    let last := UnifiedInventorySource.final model start vocabulary encoding law rounds past
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    let first := UnifiedInventoryBudget.first model start past
    let count := UnifiedInventoryBudget.span model start vocabulary encoding law rounds past
    let runtime := WithdrawalInquiryRuntime.runtime model last
    (UnifiedRecoveryRun.produce model start vocabulary encoding law past).recoveries.length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model) source first + MixedBirthPotential.capacity model ∧
    (((WithdrawalInquiryRuntime.authority model last).current.challenges).filter
      (fun row => row.2.isPending (UnifiedInventorySource.family model) source)).length +
      InventoryBirthBudget.relieved (UnifiedInventorySource.family model) source first (count + 1) ≤
        CompletedInventory.pending (UnifiedInventorySource.family model) source first + MixedBirthPotential.capacity model +
          CompletedInventory.openBorn (UnifiedInventorySource.family model) source (first + count) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model last).process.stateAt
      ((WithdrawalInquiryRuntime.facade model last).process.successor runtime.state) := by
  dsimp only
  have recoveries := MixedBirthBudget.all_actual_mixed_recoveries_are_funded_by_initial_pending_and_finite_source_capacity
    model start vocabulary encoding law (JointResponse.fuel model start past) past delay compliant
  have born := MixedBirthBudget.the_actual_mixed_native_arrivals_have_a_finite_source_capacity
    model start vocabulary encoding law (JointResponse.fuel model start past) past delay compliant
  have census := UnifiedInventoryConsumer.the_full_final_root_census_has_exact_balance_including_its_additional_birth_slice
    model start vocabulary encoding law past
  dsimp only at census
  rw [InventoryBirthBudget.arrivals] at census
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next model
    (UnifiedInventorySource.final model start vocabulary encoding law (JointResponse.fuel model start past) past)
  refine ⟨recoveries, ?_, rooted.2.2.2.1, rooted.2.2.2.2⟩
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedBirthConsumer
