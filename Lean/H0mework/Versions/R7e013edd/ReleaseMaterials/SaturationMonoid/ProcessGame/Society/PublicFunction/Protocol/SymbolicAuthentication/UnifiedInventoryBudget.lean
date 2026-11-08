import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventorySource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryBudget
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

section Visits
variable {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (source : Index)

theorem productive_is_the_exact_actual_visit_count (first count : Nat) :
    InventoryBirthBudget.productive bound source first count =
      ((List.range count).filter (fun offset => decide (0 < CompletedInventory.closedOld bound source (first + offset)))).length := by
  induction count with
  | zero => rfl
  | succ count ih =>
    by_cases positive : 0 < CompletedInventory.closedOld bound source (first + count)
    · simp [InventoryBirthBudget.productive, ih, List.range_succ, positive]
    · simp [InventoryBirthBudget.productive, ih, List.range_succ, positive]
end Visits

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev first (past : JointResponse.Stages model) := EventStep.boundary (EventHistory.execute start past)
abbrev span (rounds : Nat) (past : JointResponse.Stages model) :=
  (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages.length - past.length

theorem all_actual_recoveries_are_paid_by_distinct_productive_visits_of_one_final_source
    (rounds : Nat) (past : JointResponse.Stages model) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.length ≤
      InventoryBirthBudget.productive (UnifiedInventorySource.family model)
        (UnifiedInventorySource.inputs model start vocabulary encoding law rounds past)
        (first model start past) (span model start vocabulary encoding law rounds past) := by
  let result := UnifiedRecoveryRun.run model start vocabulary encoding law rounds past
  let cut := UnifiedInventorySource.cut model start vocabulary encoding law
  let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
  let begin := first model start past
  let count := span model start vocabulary encoding law rounds past
  let visits := ((List.range count).filter (fun offset => decide
    (0 < CompletedInventory.closedOld (UnifiedInventorySource.family model) source (begin + offset)))).map (begin + ·)
  have subset : (result.recoveries.map cut).toFinset ⊆ visits.toFinset := by
    intro point member
    obtain ⟨entry, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    have bounds := UnifiedInventorySource.every_recovery_visit_is_inside_the_same_actual_completed_window
      model start vocabulary encoding law rounds past entry present
    have productive := (UnifiedInventorySource.each_actual_recovery_spends_the_one_final_source_inventory
      model start vocabulary encoding law rounds past entry present).1
    have old := IncidentChallenge.execution_advances_the_actual_boundary model start past
    have last := IncidentChallenge.execution_advances_the_actual_boundary model start result.stages
    have kept := (UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past).length_le
    have inside : cut entry - begin < count := by
      change begin ≤ cut entry ∧ cut entry < EventStep.boundary (UnifiedInventorySource.final model start vocabulary encoding law rounds past) at bounds
      change EventStep.boundary (EventHistory.execute start result.stages) = _ at last
      dsimp only [begin, first, count, span, result, UnifiedInventorySource.final, cut] at bounds old last kept ⊢
      omega
    have sameCut : begin + (cut entry - begin) = cut entry := by
      change begin ≤ cut entry ∧ _ at bounds
      omega
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨cut entry - begin, List.mem_filter.mpr ⟨List.mem_range.mpr inside, ?_⟩, ?_⟩
    · apply decide_eq_true
      rw [sameCut]
      exact productive
    · exact sameCut.trans same
  have distinct := UnifiedInventorySource.every_recovery_has_its_own_distinct_completed_visit
    model start vocabulary encoding law rounds past
  have counted := (Finset.card_le_card subset).trans visits.toFinset_card_le
  rw [List.toFinset_card_of_nodup distinct, List.length_map] at counted
  have visitCount : visits.length = InventoryBirthBudget.productive (UnifiedInventorySource.family model) source begin count := by
    rw [productive_is_the_exact_actual_visit_count]
    exact List.length_map ..
  exact counted.trans_eq visitCount

theorem the_actual_mixed_recovery_budget_is_initial_pending_plus_actual_open_births
    (rounds : Nat) (past : JointResponse.Stages model) :
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    let begin := first model start past
    let count := span model start vocabulary encoding law rounds past
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model) source begin +
        InventoryBirthBudget.arrivals (UnifiedInventorySource.family model) source begin count :=
  (all_actual_recoveries_are_paid_by_distinct_productive_visits_of_one_final_source model start vocabulary encoding law rounds past).trans
    (InventoryBirthBudget.every_actual_window_has_a_source_generated_productive_visit_budget _ _ _ _)

theorem the_one_actual_final_source_has_exact_birth_disposition_and_residual_balance
    (rounds : Nat) (past : JointResponse.Stages model) :
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    let begin := first model start past
    let count := span model start vocabulary encoding law rounds past
    CompletedInventory.pending (UnifiedInventorySource.family model) source (begin + count) +
      InventoryBirthBudget.relieved (UnifiedInventorySource.family model) source begin count =
    CompletedInventory.pending (UnifiedInventorySource.family model) source begin +
      InventoryBirthBudget.arrivals (UnifiedInventorySource.family model) source begin count :=
  InventoryBirthBudget.the_complete_source_window_has_exact_birth_disposition_and_residual_balance _ _ _ _

theorem the_final_root_census_extends_one_slice_beyond_the_completed_window
    (rounds : Nat) (past : JointResponse.Stages model) :
    first model start past + span model start vocabulary encoding law rounds past + 1 =
      WithdrawalInquiryRuntime.depth model (UnifiedInventorySource.final model start vocabulary encoding law rounds past) + 2 := by
  have kept := (UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past).length_le
  have initial := IncidentChallenge.execution_advances_the_actual_boundary model start past
  have last := IncidentChallenge.execution_advances_the_actual_boundary model start
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages
  dsimp only [first, span, UnifiedInventorySource.final, WithdrawalInquiryRuntime.depth, EventStep.boundary] at initial last ⊢
  omega

theorem the_recovery_budget_retains_every_birth_in_the_final_root_census
    (rounds : Nat) (past : JointResponse.Stages model) :
    let source := UnifiedInventorySource.inputs model start vocabulary encoding law rounds past
    let begin := first model start past
    let count := span model start vocabulary encoding law rounds past
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.length ≤
      CompletedInventory.pending (UnifiedInventorySource.family model) source begin +
        InventoryBirthBudget.arrivals (UnifiedInventorySource.family model) source begin (count + 1) := by
  dsimp only
  have actual := the_actual_mixed_recovery_budget_is_initial_pending_plus_actual_open_births model start vocabulary encoding law rounds past
  rw [InventoryBirthBudget.arrivals]
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventoryBudget
