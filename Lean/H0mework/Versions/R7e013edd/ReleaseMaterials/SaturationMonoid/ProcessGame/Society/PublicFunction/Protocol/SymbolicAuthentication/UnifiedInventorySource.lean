import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualInventoryPrefix

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventorySource
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

abbrev family := ActualInventoryPrefix.family model
abbrev final (rounds : Nat) (past : JointResponse.Stages model) :=
  EventHistory.execute start (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages
abbrev inputs (rounds : Nat) (past : JointResponse.Stages model) :=
  ActualInventoryPrefix.inputs model (final model start vocabulary encoding law rounds past)
abbrev cut (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law) :=
  EventStep.boundary (EventHistory.execute start entry.past)

theorem each_actual_recovery_spends_the_one_final_source_inventory
    (rounds : Nat) (past : JointResponse.Stages model)
    (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law)
    (member : entry ∈ (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries) :
    let visit := cut model start vocabulary encoding law entry
    let source := inputs model start vocabulary encoding law rounds past
    0 < CompletedInventory.closedOld (family model) source visit ∧
    CompletedInventory.openBorn (family model) source visit = 0 ∧
    CompletedInventory.pending (family model) source (visit + 1) < CompletedInventory.pending (family model) source visit := by
  dsimp only
  have actual := (UnifiedRecoveryTrace.every_record_is_on_the_same_actual_execution
    model start vocabulary encoding law rounds past entry member).2
  obtain ⟨tail, same⟩ := actual
  let recovered := NativeRecovery.full model start entry.past vocabulary encoding law entry.answer
  let current := EventHistory.execute start recovered
  have finalExact : final model start vocabulary encoding law rounds past = EventHistory.execute current tail := by
    change EventHistory.execute start _ = _
    rw [← same, StageQueue.execute_append]
  have boundary : EventStep.boundary current = cut model start vocabulary encoding law entry + 1 := by
    change EventStep.boundary (EventHistory.execute start (entry.past ++ [_])) = _
    rw [StageQueue.execute_append]
    rfl
  have aligned := ActualInventoryPrefix.one_actual_extension_preserves_the_complete_inventory_slices model current tail
    (cut model start vocabulary encoding law entry) (by omega)
  rw [← finalExact] at aligned
  have descent := RecoveryInventory.actual_recovery_strictly_lowers_the_entire_completed_pending_inventory
    model start entry.past vocabulary encoding law entry.answer
  have newborn := RecoveryInventory.the_actual_recovery_does_not_refill_pending_with_its_own_newborn
    model start entry.past vocabulary encoding law entry.answer
  have balance := CompletedInventory.every_completed_cut_has_exact_source_birth_and_disposition_balance
    (family model) (ActualInventoryPrefix.inputs model current) (cut model start vocabulary encoding law entry)
  change CompletedInventory.pending (family model) (ActualInventoryPrefix.inputs model current)
    (cut model start vocabulary encoding law entry + 1) <
    CompletedInventory.pending (family model) (ActualInventoryPrefix.inputs model current)
      (cut model start vocabulary encoding law entry) at descent
  change CompletedInventory.openBorn (family model) (ActualInventoryPrefix.inputs model current)
    (cut model start vocabulary encoding law entry) = 0 at newborn
  change _ ∧ _ ∧ _
  rw [aligned.1, aligned.2.1, aligned.2.2.1, aligned.2.2.2]
  dsimp only [family] at balance descent newborn ⊢
  exact ⟨by omega, newborn, descent⟩

theorem every_recovery_has_its_own_distinct_completed_visit
    (rounds : Nat) (past : JointResponse.Stages model) :
    ((UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries.map
      (cut model start vocabulary encoding law)).Nodup := by
  induction rounds generalizing past with
  | zero => simp only [UnifiedRecoveryRun.run]; split_ifs <;> exact List.nodup_nil
  | succ rounds ih =>
    cases selected : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [UnifiedRecoveryRun.run, selected, List.map_nil]; exact List.nodup_nil
    | exhausted empty => simp only [UnifiedRecoveryRun.run, selected, List.map_nil]; exact List.nodup_nil
    | advance action =>
      cases action with
      | original action =>
        simp only [UnifiedRecoveryRun.run, selected, UnifiedRecoveryRun.events, List.nil_append]
        exact ih _
      | recovery answer =>
        simp only [UnifiedRecoveryRun.run, selected, UnifiedRecoveryRun.events, List.singleton_append, List.map_cons]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih _⟩
        intro repeated
        obtain ⟨entry, member, same⟩ := List.mem_map.mp repeated
        have ordered := (UnifiedRecoveryTrace.every_record_is_on_the_same_actual_execution model start vocabulary encoding law rounds
          (NativeRecovery.full model start past vocabulary encoding law answer) entry member).1.length_le
        have size : (NativeRecovery.full model start past vocabulary encoding law answer).length = past.length + 1 := by
          change (past ++ [_]).length = _
          simp only [List.length_append, List.length_singleton]
        have before := IncidentChallenge.execution_advances_the_actual_boundary model start past
        have after := IncidentChallenge.execution_advances_the_actual_boundary model start entry.past
        change EventStep.boundary (EventHistory.execute start entry.past) = EventStep.boundary (EventHistory.execute start past) at same
        omega

theorem every_recovery_visit_is_inside_the_same_actual_completed_window
    (rounds : Nat) (past : JointResponse.Stages model)
    (entry : UnifiedRecoveryRun.RecoveryEvent model start vocabulary encoding law)
    (member : entry ∈ (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).recoveries) :
    EventStep.boundary (EventHistory.execute start past) ≤ cut model start vocabulary encoding law entry ∧
      cut model start vocabulary encoding law entry < EventStep.boundary (final model start vocabulary encoding law rounds past) := by
  have prefixes := UnifiedRecoveryTrace.every_record_is_on_the_same_actual_execution model start vocabulary encoding law rounds past entry member
  have before := prefixes.1.length_le
  have after := prefixes.2.length_le
  have size : (NativeRecovery.full model start entry.past vocabulary encoding law entry.answer).length = entry.past.length + 1 := by
    change (entry.past ++ [_]).length = _
    simp only [List.length_append, List.length_singleton]
  have first := IncidentChallenge.execution_advances_the_actual_boundary model start past
  have middle := IncidentChallenge.execution_advances_the_actual_boundary model start entry.past
  have last := IncidentChallenge.execution_advances_the_actual_boundary model start
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages
  change _ ≤ EventStep.boundary (EventHistory.execute start entry.past) ∧
    EventStep.boundary (EventHistory.execute start entry.past) <
      EventStep.boundary (EventHistory.execute start (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages)
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedInventorySource
