import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceTrace

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceInventory
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

theorem every_actual_service_spends_the_same_final_source_inventory
    (rounds : Nat) (past : JointResponse.Stages model) (entry : NativeServiceTrace.Entry model start vocabulary encoding law)
    (member : entry ∈ NativeServiceTrace.records model start vocabulary encoding law rounds past) :
    let visit := NativeServiceTrace.cut model start vocabulary encoding law entry
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    0 < CompletedInventory.closedOld (UnifiedInventorySource.family model) source visit ∧
    CompletedInventory.openBorn (UnifiedInventorySource.family model) source visit = 0 ∧
    CompletedInventory.pending (UnifiedInventorySource.family model) source (visit + 1) <
      CompletedInventory.pending (UnifiedInventorySource.family model) source visit := by
  dsimp only
  obtain ⟨tail, same⟩ := (NativeServiceTrace.every_service_record_is_on_the_same_actual_mixed_execution
    model start vocabulary encoding law rounds past entry member).2
  let current := NativeServiceSource.after model start vocabulary encoding law entry.past entry.receipt.action
  have finalExact : UnifiedInventorySource.final model start vocabulary encoding law rounds past = EventHistory.execute current tail := by
    change EventHistory.execute start _ = _
    rw [← same, OriginQueue.execute_append]
  have boundary := (NativeServiceSource.every_record_is_one_actual_native_stage model start vocabulary encoding law entry.past entry.receipt).2
  have aligned := ActualInventoryPrefix.one_actual_extension_preserves_the_complete_inventory_slices model current tail
    (NativeServiceTrace.cut model start vocabulary encoding law entry) (by
      change NativeServiceSource.visit model start entry.past + 1 ≤ _
      exact Nat.le_of_eq boundary.symm)
  rw [← finalExact] at aligned
  have progress := NativeServiceSource.every_record_has_strict_completed_inventory_progress model start vocabulary encoding law entry.past entry.receipt
  rw [aligned.1, aligned.2.1, aligned.2.2.1, aligned.2.2.2]
  exact progress

theorem all_actual_native_services_are_paid_by_distinct_productive_visits
    (rounds : Nat) (past : JointResponse.Stages model) :
    (NativeServiceTrace.records model start vocabulary encoding law rounds past).length ≤
      InventoryBirthBudget.productive (UnifiedInventorySource.family model)
        (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
        (UnifiedInventoryBudget.first model start past) (UnifiedInventoryBudget.span model start vocabulary encoding law rounds past) := by
  let entries := NativeServiceTrace.records model start vocabulary encoding law rounds past
  let cut := NativeServiceTrace.cut model start vocabulary encoding law
  let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
  let begin := UnifiedInventoryBudget.first model start past
  let count := UnifiedInventoryBudget.span model start vocabulary encoding law rounds past
  let visits := ((List.range count).filter (fun offset => decide
    (0 < CompletedInventory.closedOld (UnifiedInventorySource.family model) source (begin + offset)))).map (begin + ·)
  have subset : (entries.map cut).toFinset ⊆ visits.toFinset := by
    intro point member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have bounds := NativeServiceTrace.every_record_is_inside_the_actual_completed_window model start vocabulary encoding law rounds past entry present
    have productive := (every_actual_service_spends_the_same_final_source_inventory model start vocabulary encoding law rounds past entry present).1
    have old := IncidentChallenge.execution_advances_the_actual_boundary model start past
    have last := IncidentChallenge.execution_advances_the_actual_boundary model start
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages
    have kept := (UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past).length_le
    have inside : cut entry - begin < count := by
      dsimp only [cut, begin, count, UnifiedInventoryBudget.span, UnifiedInventoryBudget.first, UnifiedInventorySource.final] at bounds old last kept ⊢
      omega
    have sameCut : begin + (cut entry - begin) = cut entry := by
      change begin ≤ cut entry ∧ _ at bounds
      omega
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨cut entry - begin, List.mem_filter.mpr ⟨List.mem_range.mpr inside, ?_⟩, sameCut.trans same⟩
    apply decide_eq_true
    rw [sameCut]
    exact productive
  have distinct := NativeServiceTrace.every_record_has_a_distinct_completed_service_visit model start vocabulary encoding law rounds past
  have counted := (Finset.card_le_card subset).trans visits.toFinset_card_le
  rw [List.toFinset_card_of_nodup distinct, List.length_map] at counted
  have visitCount : visits.length = InventoryBirthBudget.productive (UnifiedInventorySource.family model) source begin count := by
    rw [UnifiedInventoryBudget.productive_is_the_exact_actual_visit_count]
    exact List.length_map ..
  exact counted.trans_eq visitCount

theorem the_complete_mixed_service_budget_is_initial_pending_plus_finite_source_capacity
    (rounds : Nat) (past : JointResponse.Stages model) (delay : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delay
      (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages) :
    (NativeServiceTrace.records model start vocabulary encoding law rounds past).length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model)
        (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
        (UnifiedInventoryBudget.first model start past) + MixedBirthPotential.capacity model := by
  have actual := all_actual_native_services_are_paid_by_distinct_productive_visits model start vocabulary encoding law rounds past
  have inventory := InventoryBirthBudget.every_actual_window_has_a_source_generated_productive_visit_budget
    (UnifiedInventorySource.family model) (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
    (UnifiedInventoryBudget.first model start past) (UnifiedInventoryBudget.span model start vocabulary encoding law rounds past)
  have born := MixedBirthBudget.the_actual_mixed_native_arrivals_have_a_finite_source_capacity model start vocabulary encoding law rounds past delay compliant
  exact (actual.trans inventory).trans (Nat.add_le_add_left born _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceInventory
