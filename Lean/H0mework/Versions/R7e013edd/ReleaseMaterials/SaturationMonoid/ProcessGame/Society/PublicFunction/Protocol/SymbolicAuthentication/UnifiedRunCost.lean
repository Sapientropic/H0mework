import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunPrefix

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunCost
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

theorem each_actual_dispatch_has_a_source_generated_stage_cost
    (past : JointResponse.Stages model) (action : UnifiedRecoveryDispatch.Action model start vocabulary encoding law past) :
    (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action).length ≤
      past.length + CommunicationWorkBudget.slotAllowance model start := by
  have room : 1 ≤ CommunicationWorkBudget.slotAllowance model start := by
    unfold CommunicationWorkBudget.slotAllowance; omega
  cases action with
  | recovery answer =>
    change (past ++ [_]).length ≤ _
    simp only [List.length_append, List.length_singleton]
    omega
  | original action =>
    cases action with
    | communication action =>
      cases action with
      | retry answer selected =>
        exact CommunicationWorkBudget.each_actual_retry_has_a_uniform_original_roster_cost model start vocabulary encoding law past answer
      | conflict answer selected =>
        change (past ++ [_]).length ≤ _
        simp only [List.length_append, List.length_singleton]; omega
      | rejection answer selected =>
        change (past ++ [_]).length ≤ _
        simp only [List.length_append, List.length_singleton]; omega
      | wait live =>
        change (past ++ [_]).length ≤ _
        simp only [List.length_append, List.length_singleton]; omega
    | withdrawal ready accepted selected =>
      change (past ++ [_]).length ≤ _
      simp only [List.length_append, List.length_singleton]; omega
    | refused ready denied selected =>
      change (past ++ [_]).length ≤ _
      simp only [List.length_append, List.length_singleton]; omega
    | wait live =>
      change (past ++ [_]).length ≤ _
      simp only [List.length_append, List.length_singleton]; omega

theorem actual_invocations_pay_all_physical_stages (rounds : Nat) (past : JointResponse.Stages model) :
    (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages.length ≤
      past.length + rounds * CommunicationWorkBudget.slotAllowance model start := by
  induction rounds generalizing past with
  | zero =>
    simp only [UnifiedRecoveryRun.run]; split_ifs <;> simp
  | succ rounds ih =>
    cases actual : UnifiedRecoveryDispatch.step model start vocabulary encoding law past with
    | clear complete => simp only [UnifiedRecoveryRun.run, actual]; omega
    | exhausted empty => simp only [UnifiedRecoveryRun.run, actual]; omega
    | advance action =>
      have next := ih (UnifiedRecoveryDispatch.after model start vocabulary encoding law past action)
      have cost := each_actual_dispatch_has_a_source_generated_stage_cost model start vocabulary encoding law past action
      simp only [UnifiedRecoveryRun.run, actual]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem a_source_reserve_keeps_every_actual_prefix_live
    (rounds : Nat) (past : JointResponse.Stages model)
    (reserve : rounds * CommunicationWorkBudget.slotAllowance model start < JointResponse.fuel model start past) :
    0 < JointResponse.fuel model start (UnifiedRecoveryRun.run model start vocabulary encoding law rounds past).stages := by
  obtain ⟨tail, same⟩ := UnifiedRecoveryRun.every_run_keeps_the_whole_actual_history model start vocabulary encoding law rounds past
  have cost := actual_invocations_pay_all_physical_stages model start vocabulary encoding law rounds past
  rw [← same, List.length_append] at cost
  rw [← same]
  change 0 < UnifiedResponse.fuel model start (past ++ tail)
  rw [UnifiedResponse.fuel_after_actual_extension]
  change rounds * CommunicationWorkBudget.slotAllowance model start < UnifiedResponse.fuel model start past at reserve
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRunCost
