import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentRegistration

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseBudget
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

abbrev count (past : List (EventHistory.Stage (code := model.source.code))) :=
  (IncidentResponse.journal model start past vocabulary encoding law).length +
    (RejectionResponse.journal model start past vocabulary encoding law).length
abbrev capacity := IncidentInventory.capacity (code := model.source.code) +
  AdaptiveReceptionBudget.capacity (code := model.source.code)
def remaining (past : List (EventHistory.Stage (code := model.source.code))) :=
  capacity model - count model start vocabulary encoding law past

theorem every_actual_compliant_history_has_a_joint_registration_budget
    (past : List (EventHistory.Stage (code := model.source.code)))
    (allowance : Nat) (compliant : AdaptiveRejectionHistory.Compliant start allowance past) :
    count model start vocabulary encoding law past ≤ capacity model :=
  Nat.add_le_add (IncidentRegistration.the_number_of_actual_native_responses_has_the_original_source_budget
    model start vocabulary encoding law past)
    (RejectionRegistration.the_number_of_actual_native_responses_has_the_original_source_budget
      model start vocabulary encoding law past allowance compliant)

theorem actual_extension_preserves_both_original_journals
    (past later : List (EventHistory.Stage (code := model.source.code))) (ordered : past <+: later) :
    (IncidentResponse.journal model start past vocabulary encoding law).length ≤
      (IncidentResponse.journal model start later vocabulary encoding law).length ∧
    (RejectionResponse.journal model start past vocabulary encoding law).length ≤
      (RejectionResponse.journal model start later vocabulary encoding law).length := by
  obtain ⟨more, rfl⟩ := ordered
  exact ⟨(IncidentRegistration.actual_history_extension_preserves_the_literal_original_journal
    model start vocabulary encoding law past more).length_le,
    (RejectionRegistration.actual_history_extension_preserves_the_literal_original_journal
      model start vocabulary encoding law past more).length_le⟩

theorem count_never_decreases (past later : List (EventHistory.Stage (code := model.source.code)))
    (ordered : past <+: later) : count model start vocabulary encoding law past ≤ count model start vocabulary encoding law later := by
  have both := actual_extension_preserves_both_original_journals model start vocabulary encoding law past later ordered
  exact Nat.add_le_add both.1 both.2

def responseKind : JointResponse.Kind → Bool
  | .communication .conflict | .communication .rejection => true
  | _ => false

def responseSteps (trace : List JointResponse.Kind) := (trace.filter responseKind).length

theorem an_actual_response_action_generates_registration_progress
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (response : responseKind (JointResponse.kind model start vocabulary encoding law action) = true) :
    count model start vocabulary encoding law past + 1 ≤
      count model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) := by
  have both := actual_extension_preserves_both_original_journals model start vocabulary encoding law _ _
    (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action)
  cases action with
  | communication action =>
    cases action with
    | conflict answer selected =>
      have grew := congrArg List.length (IncidentResponse.a_generated_response_is_registered_once
        model start past vocabulary encoding law answer (OriginQueue.environment start) selected)
      simp only [List.length_map, List.length_append, List.length_singleton] at grew
      change (IncidentResponse.journal model start past vocabulary encoding law).length ≤
        (IncidentResponse.journal model start (past ++ [_]) vocabulary encoding law).length ∧
        (RejectionResponse.journal model start past vocabulary encoding law).length ≤
        (RejectionResponse.journal model start (past ++ [_]) vocabulary encoding law).length at both
      dsimp only [count, JointResponse.after, UnifiedResponse.after] at grew both ⊢
      omega
    | rejection answer selected =>
      have grew := congrArg List.length (RejectionResponse.a_generated_response_is_registered_once
        model start past vocabulary encoding law answer (OriginQueue.environment start) selected)
      simp only [List.length_map, List.length_append, List.length_singleton] at grew
      change (IncidentResponse.journal model start past vocabulary encoding law).length ≤
        (IncidentResponse.journal model start (past ++ [_]) vocabulary encoding law).length ∧
        (RejectionResponse.journal model start past vocabulary encoding law).length ≤
        (RejectionResponse.journal model start (past ++ [_]) vocabulary encoding law).length at both
      dsimp only [count, JointResponse.after, UnifiedResponse.after] at grew both ⊢
      omega
    | retry answer selected => contradiction
    | wait live => contradiction
  | withdrawal ready accepted selected => contradiction
  | refused ready denied selected => contradiction
  | wait live => contradiction

theorem an_actual_compliant_response_strictly_consumes_the_joint_capacity
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (response : responseKind (JointResponse.kind model start vocabulary encoding law action) = true)
    (allowance : Nat) (compliant : AdaptiveRejectionHistory.Compliant start allowance
      (JointResponse.after model start vocabulary encoding law past action)) :
    remaining model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) <
      remaining model start vocabulary encoding law past := by
  have grew := an_actual_response_action_generates_registration_progress model start vocabulary encoding law past action response
  have bound := every_actual_compliant_history_has_a_joint_registration_budget model start vocabulary encoding law _ allowance compliant
  dsimp only [remaining, count] at grew bound ⊢
  omega

theorem every_original_run_pays_for_its_actual_response_steps
    (rounds : Nat) (past : JointResponse.Stages model) :
    count model start vocabulary encoding law past +
      responseSteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace ≤
      count model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages := by
  induction rounds generalizing past with
  | zero =>
    simp only [JointResponseRun.run]
    split
    · simp only [responseSteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    · split <;> simp only [responseSteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [JointResponseRun.run, actual, responseSteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | exhausted empty => simp only [JointResponseRun.run, actual, responseSteps, List.filter_nil, List.length_nil, Nat.add_zero, Nat.le_refl]
    | advance action =>
      have next := ih (JointResponse.after model start vocabulary encoding law past action)
      have kept := count_never_decreases model start vocabulary encoding law _ _
        (JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action)
      simp only [JointResponseRun.run, actual]
      by_cases response : responseKind (JointResponse.kind model start vocabulary encoding law action) = true
      · have grew := an_actual_response_action_generates_registration_progress model start vocabulary encoding law past action response
        simp only [responseSteps, List.filter_cons, response, if_true, List.length_cons] at *
        omega
      · have quiet : responseKind (JointResponse.kind model start vocabulary encoding law action) = false := Bool.eq_false_iff.mpr response
        simp only [responseSteps, List.filter_cons, quiet, Bool.false_eq_true, if_false] at *
        omega

theorem the_actual_joint_run_has_a_source_generated_response_execution_budget
    (rounds : Nat) (past : JointResponse.Stages model) (allowance : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start allowance
      (JointResponseRun.run model start vocabulary encoding law rounds past).stages) :
    count model start vocabulary encoding law past +
      responseSteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace ≤ capacity model :=
  (every_original_run_pays_for_its_actual_response_steps model start vocabulary encoding law rounds past).trans
    (every_actual_compliant_history_has_a_joint_registration_budget model start vocabulary encoding law _ allowance compliant)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseBudget
