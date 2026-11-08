import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryProgress

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryExecutionBudget
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

abbrev count (past : JointResponse.Stages model) := (DutyConfirmation.contents start vocabulary encoding law past).card
def retryKind : JointResponse.Kind → Bool
  | .communication .retry => true
  | _ => false
def retrySteps (trace : List JointResponse.Kind) := (trace.filter retryKind).length

theorem count_never_decreases (past later : JointResponse.Stages model) (ordered : past <+: later) :
    count model start vocabulary encoding law past ≤ count model start vocabulary encoding law later :=
  Finset.card_le_card (DutyConfirmation.confirmed_contents_survive_actual_extension start vocabulary encoding law past later ordered)

theorem every_actual_retry_action_generates_confirmation_progress
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (retry : retryKind (JointResponse.kind model start vocabulary encoding law action) = true) :
    count model start vocabulary encoding law past + 1 ≤
      count model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) := by
  cases action with
  | communication action =>
    cases action with
    | conflict answer selected => contradiction
    | rejection answer selected => contradiction
    | retry answer selected => exact RetryProgress.every_actual_ready_retry_generates_strict_confirmation_progress encoding start vocabulary law past answer
    | wait live => contradiction
  | withdrawal ready accepted selected => contradiction
  | refused ready denied selected => contradiction
  | wait live => contradiction

theorem every_original_run_pays_for_its_actual_retries
    (rounds : Nat) (past : JointResponse.Stages model) :
    count model start vocabulary encoding law past +
      retrySteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace ≤
      count model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero =>
    simp only [JointResponseRun.run]
    split
    · simp only [retrySteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    · split <;> simp only [retrySteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [JointResponseRun.run, actual, retrySteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | exhausted empty => simp only [JointResponseRun.run, actual, retrySteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | advance action =>
      have next := ih (JointResponse.after model start vocabulary encoding law past action)
      have kept := count_never_decreases model start vocabulary encoding law _ _
        (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action)
      simp only [JointResponseRun.run, actual]
      by_cases retry : retryKind (JointResponse.kind model start vocabulary encoding law action) = true
      · have grew := every_actual_retry_action_generates_confirmation_progress model start vocabulary encoding law past action retry
        simp only [retrySteps, List.filter_cons, retry, if_true, List.length_cons] at *
        omega
      · have quiet := Bool.eq_false_iff.mpr retry
        simp only [retrySteps, List.filter_cons, quiet, Bool.false_eq_true, if_false] at *
        omega

theorem every_actual_joint_run_has_a_source_generated_retry_budget
    (rounds : Nat) (past : JointResponse.Stages model) :
    count model start vocabulary encoding law past +
      retrySteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace ≤
      RetryProgress.capacity (code := model.source.code) :=
  (every_original_run_pays_for_its_actual_retries model start vocabulary encoding law rounds past).trans
    (RetryProgress.confirmed_contents_have_a_source_generated_budget encoding start vocabulary law _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RetryExecutionBudget
