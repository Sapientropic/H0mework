import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryExecutionBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationWorkBudget
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

abbrev capacity := UnifiedResponseBudget.capacity model + RetryProgress.capacity (code := model.source.code)
abbrev count (past : JointResponse.Stages model) := UnifiedResponseBudget.count model start vocabulary encoding law past +
  RetryExecutionBudget.count model start vocabulary encoding law past
def workSteps (trace : List JointResponse.Kind) := UnifiedResponseBudget.responseSteps trace + RetryExecutionBudget.retrySteps trace

theorem actual_joint_communication_work_has_a_source_generated_budget
    (rounds : Nat) (past : JointResponse.Stages model) (allowance : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start allowance
      (JointResponseRun.run model start vocabulary encoding law rounds past).stages) :
    count model start vocabulary encoding law past +
      workSteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace ≤ capacity model := by
  have responses := UnifiedResponseBudget.the_actual_joint_run_has_a_source_generated_response_execution_budget
    model start vocabulary encoding law rounds past allowance compliant
  have retries := RetryExecutionBudget.every_actual_joint_run_has_a_source_generated_retry_budget
    model start vocabulary encoding law rounds past
  dsimp only [count, workSteps, capacity]
  omega

private theorem the_original_roster_is_preserved (past : JointResponse.Stages model) :
    (EventHistory.execute start past).ownerStart = start.ownerStart := by
  induction past generalizing start with
  | nil => rfl
  | cons stage tail ih => exact ih (start.after stage.1 stage.2)

def slotAllowance := start.ownerStart + 4 * model.source.code.sites + 1

theorem each_actual_retry_has_a_uniform_original_roster_cost
    (past : JointResponse.Stages model) (answer : TimedRetry.Ready start past vocabulary encoding law) :
    answer.stages.length ≤ past.length + slotAllowance model start := by
  have shape := TimedRetry.retry_has_a_bounded_source_schedule start past vocabulary encoding law answer
  have clock := shape.2
  have roster : (TimedRetry.current start past).ownerStart = start.ownerStart := the_original_roster_is_preserved model start past
  rw [roster] at clock
  have clamped := Nat.sub_le start.ownerStart (EventStep.seed (TimedRetry.current start past)).history.length
  dsimp only [slotAllowance]
  omega

def actionCost (past : JointResponse.Stages model) : JointResponse.Action model start vocabulary encoding law past → Nat
  | .communication (.retry answer _) => answer.stages.length - past.length
  | _ => 0

-- This readout follows the original step and records only the actual retry macro lengths.
def retryCost : Nat → JointResponse.Stages model → Nat
  | 0, _ => 0
  | rounds + 1, past => match JointResponse.step model start vocabulary encoding law past with
    | .advance action => actionCost model start vocabulary encoding law past action +
        retryCost rounds (JointResponse.after model start vocabulary encoding law past action)
    | _ => 0

private theorem action_cost_is_bounded (past : JointResponse.Stages model)
    (action : JointResponse.Action model start vocabulary encoding law past) :
    actionCost model start vocabulary encoding law past action ≤
      if RetryExecutionBudget.retryKind (JointResponse.kind model start vocabulary encoding law action) then slotAllowance model start else 0 := by
  cases action with
  | communication action =>
    cases action with
    | conflict answer selected => exact Nat.le_refl 0
    | rejection answer selected => exact Nat.le_refl 0
    | retry answer selected =>
      change answer.stages.length - past.length ≤ slotAllowance model start
      have bounded := each_actual_retry_has_a_uniform_original_roster_cost model start vocabulary encoding law past answer
      omega
    | wait live => exact Nat.le_refl 0
  | withdrawal ready accepted selected => exact Nat.le_refl 0
  | refused ready denied selected => exact Nat.le_refl 0
  | wait live => exact Nat.le_refl 0

theorem actual_retry_cost_is_paid_by_the_original_retry_trace
    (rounds : Nat) (past : JointResponse.Stages model) :
    retryCost model start vocabulary encoding law rounds past ≤
      RetryExecutionBudget.retrySteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace * slotAllowance model start := by
  induction rounds generalizing past with
  | zero =>
    simp only [retryCost, JointResponseRun.run]
    split
    · exact Nat.zero_le _
    · split <;> exact Nat.zero_le _
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [retryCost, actual]; exact Nat.zero_le _
    | exhausted empty => simp only [retryCost, actual]; exact Nat.zero_le _
    | advance action =>
      have next := ih (JointResponse.after model start vocabulary encoding law past action)
      have paid := action_cost_is_bounded model start vocabulary encoding law past action
      simp only [retryCost, JointResponseRun.run, actual]
      by_cases retry : RetryExecutionBudget.retryKind (JointResponse.kind model start vocabulary encoding law action) = true
      · simp only [RetryExecutionBudget.retrySteps, List.filter_cons, retry, if_true, List.length_cons,
          Nat.add_mul, Nat.one_mul] at paid next ⊢
        omega
      · have quiet := Bool.eq_false_iff.mpr retry
        simp only [RetryExecutionBudget.retrySteps, List.filter_cons, quiet, Bool.false_eq_true, if_false] at paid next ⊢
        omega

theorem every_actual_retry_schedule_has_a_source_generated_total_cost
    (rounds : Nat) (past : JointResponse.Stages model) :
    retryCost model start vocabulary encoding law rounds past ≤
      RetryProgress.capacity (code := model.source.code) * slotAllowance model start := by
  have budget := RetryExecutionBudget.every_actual_joint_run_has_a_source_generated_retry_budget model start vocabulary encoding law rounds past
  have steps : RetryExecutionBudget.retrySteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace ≤
      RetryProgress.capacity (code := model.source.code) := by omega
  exact (actual_retry_cost_is_paid_by_the_original_retry_trace model start vocabulary encoding law rounds past).trans
    (Nat.mul_le_mul_right _ steps)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CommunicationWorkBudget
