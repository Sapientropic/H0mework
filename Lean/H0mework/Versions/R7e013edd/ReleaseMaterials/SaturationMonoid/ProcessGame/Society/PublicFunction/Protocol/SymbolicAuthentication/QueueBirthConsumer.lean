import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open Mandate.Challenge QueueBirthBudget

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (origin : Cursor model.source.code) (past : JointResponse.Stages model)

abbrev cursor := EventHistory.execute origin past
abbrev cap := (QueueScheduler.admitted model.source.code).card * QueueBirthSource.cost model.source.code

theorem an_actual_prefix_generates_its_own_queue_birth_budget (count : Nat) :
    InventoryBirthBudget.arrivals (family model) (inputs model origin (cursor model origin past) count)
      (begin model (cursor model origin past)) count ≤ cap model :=
  the_actual_origin_queue_window_has_a_finite_native_arrival_bound model origin (cursor model origin past)
    (OriginQueue.an_actual_prefix_retains_the_original_baseline origin past).length_le count

theorem the_actual_completed_inventory_and_productive_visits_consume_the_finite_birth_budget (count : Nat) :
    let source := inputs model origin (cursor model origin past) count
    let first := begin model (cursor model origin past)
    CompletedInventory.pending (family model) source (first + count) +
      InventoryBirthBudget.relieved (family model) source first count ≤
        CompletedInventory.pending (family model) source first + cap model ∧
    InventoryBirthBudget.productive (family model) source first count ≤
      CompletedInventory.pending (family model) source first + cap model := by
  dsimp only
  have births := an_actual_prefix_generates_its_own_queue_birth_budget model origin past count
  have balance := InventoryBirthBudget.the_complete_source_window_has_exact_birth_disposition_and_residual_balance
    (family model) (inputs model origin (cursor model origin past) count) (begin model (cursor model origin past)) count
  have productive := InventoryBirthBudget.every_actual_window_has_a_source_generated_productive_visit_budget
    (family model) (inputs model origin (cursor model origin past) count) (begin model (cursor model origin past)) count
  constructor <;> omega

/-- The native root also reads its next slice; that birth is retained explicitly. -/
theorem the_original_root_consumes_the_queue_budget_whole_ledger_and_own_next (count : Nat) :
    let current := cursor model origin past
    let last := final model origin current count
    let source := inputs model origin current count
    let first := begin model current
    let runtime := WithdrawalInquiryRuntime.runtime model last
    (((WithdrawalInquiryRuntime.authority model last).current.challenges).filter
      (fun row => row.2.isPending (family model) source)).length +
      InventoryBirthBudget.relieved (family model) source first (count + 1) ≤
        CompletedInventory.pending (family model) source first + cap model +
          CompletedInventory.openBorn (family model) source (first + count) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model last).process.stateAt
      ((WithdrawalInquiryRuntime.facade model last).process.successor runtime.state) := by
  dsimp only
  have rooted := WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
    model (final model origin (cursor model origin past) count)
  refine ⟨?_, rooted.2.2.2.1, rooted.2.2.2.2⟩
  rw [(WithdrawalInquiryRuntime.authority model _).current_exact]
  change ((recordsAt (family model) (inputs model origin (cursor model origin past) count)
    (WithdrawalInquiryRuntime.depth model _ + 2)).filter (fun row => row.2.isPending
      (family model) (inputs model origin (cursor model origin past) count))).length + _ ≤ _
  rw [← CompletedInventory.pending_is_the_actual_census_pending_length]
  have boundary := IncidentChallenge.execution_advances_the_actual_boundary model (cursor model origin past)
    (QueueBirthSource.stages origin count)
  rw [OriginQueue.stage_count] at boundary
  have census : WithdrawalInquiryRuntime.depth model (final model origin (cursor model origin past) count) + 2 =
      begin model (cursor model origin past) + (count + 1) := by
    dsimp only [WithdrawalInquiryRuntime.depth, EventStep.boundary, final, begin] at boundary ⊢
    omega
  rw [census, InventoryBirthBudget.the_complete_source_window_has_exact_birth_disposition_and_residual_balance,
    InventoryBirthBudget.arrivals]
  have births := an_actual_prefix_generates_its_own_queue_birth_budget model origin past count
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueueBirthConsumer
