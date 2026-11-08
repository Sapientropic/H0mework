import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureHistory

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureClock
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

def tally (prior : JointResponse.Stages model) : JointResponse.Stages model → Nat
  | [] => 0
  | stage :: tail => (if SignatureEligibility.eligible model start vocabulary encoding law prior then 1 else 0) +
      tally (prior ++ [stage]) tail

theorem tally_append (prior first more : JointResponse.Stages model) :
    tally model start vocabulary encoding law prior (first ++ more) =
      tally model start vocabulary encoding law prior first + tally model start vocabulary encoding law (prior ++ first) more := by
  induction first generalizing prior with
  | nil => simp only [tally, List.nil_append, List.append_nil, Nat.zero_add]
  | cons stage tail ih => simp only [List.cons_append, tally, ih, List.append_assoc, List.nil_append, Nat.add_assoc]

theorem tally_le_length (prior more : JointResponse.Stages model) :
    tally model start vocabulary encoding law prior more ≤ more.length := by
  induction more generalizing prior with
  | nil => exact Nat.le_refl _
  | cons stage tail ih =>
    have next := ih (prior ++ [stage])
    simp only [tally, List.length_cons]
    split <;> omega

theorem an_eligible_actual_prefix_is_counted
    (past more : JointResponse.Stages model) (n : Nat) (inside : n < more.length)
    (eligible : SignatureEligibility.eligible model start vocabulary encoding law (past ++ more.take n) = true) :
    0 < tally model start vocabulary encoding law past more := by
  induction more generalizing past n with
  | nil => cases inside
  | cons stage tail ih =>
    cases n with
    | zero =>
      simp only [List.take_zero, List.append_nil] at eligible
      simp only [tally, eligible, if_true]
      omega
    | succ n =>
      have next : SignatureEligibility.eligible model start vocabulary encoding law ((past ++ [stage]) ++ tail.take n) = true := by
        simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using eligible
      have counted := ih (past ++ [stage]) n (by simp only [List.length_cons] at inside; omega) next
      simp only [tally]
      omega

theorem zero_actual_opportunities_keeps_both_original_journals
    (past more : JointResponse.Stages model) (zero : tally model start vocabulary encoding law past more = 0) :
    IncidentResponse.journal model start (past ++ more) vocabulary encoding law = IncidentResponse.journal model start past vocabulary encoding law ∧
    RejectionResponse.journal model start (past ++ more) vocabulary encoding law = RejectionResponse.journal model start past vocabulary encoding law := by
  apply SignatureHistory.a_quiet_actual_extension_keeps_both_original_journals model start vocabulary encoding law past more
  intro n inside
  cases actual : SignatureEligibility.eligible model start vocabulary encoding law (past ++ more.take n) with
  | false => rfl
  | true =>
    have positive := an_eligible_actual_prefix_is_counted model start vocabulary encoding law past more n inside actual
    omega

theorem each_original_macro_pays_for_its_signature_opportunities
    (past more : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (selected : JointResponse.step model start vocabulary encoding law past = .advance action)
    (actual : past ++ more = JointResponse.after model start vocabulary encoding law past action) :
    tally model start vocabulary encoding law past more ≤
      (if UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) then 1 else 0) +
        CommunicationWorkBudget.actionCost model start vocabulary encoding law past action := by
  by_cases retry : RetryExecutionBudget.retryKind (JointResponse.kind model start vocabulary encoding law action) = true
  · cases action with
    | communication action =>
      cases action with
      | retry answer found =>
        have bounded := tally_le_length model start vocabulary encoding law past more
        have length := congrArg List.length actual
        simp only [List.length_append] at length
        change past.length + more.length = answer.stages.length at length
        change _ ≤ _ + (answer.stages.length - past.length)
        omega
      | conflict answer found => contradiction
      | rejection answer found => contradiction
      | wait live => contradiction
    | withdrawal ready accepted found => contradiction
    | refused ready denied found => contradiction
    | wait live => contradiction
  · obtain ⟨stage, single⟩ := PhysicalOpportunityClock.every_original_nonretry_action_has_one_actual_slot
      model start vocabulary encoding law past action (Bool.eq_false_iff.mpr retry)
    have same : more = [stage] := List.append_cancel_left (actual.trans single)
    subst more
    simp only [tally, Nat.add_zero]
    by_cases eligible : SignatureEligibility.eligible model start vocabulary encoding law past = true
    · obtain ⟨chosen, found, kind⟩ := SignatureEligibility.a_primitive_signature_opportunity_selects_an_original_response_action
        model start vocabulary encoding law past eligible
      have equal := JointResponse.Step.advance.inj (found.symm.trans selected)
      subst chosen
      rw [if_pos eligible, if_pos kind]
      omega
    · rw [if_neg eligible]
      exact Nat.zero_le _

def physical (rounds : Nat) (past : JointResponse.Stages model) :=
  tally model start vocabulary encoding law past
    ((JointResponseRun.run model start vocabulary encoding law rounds past).stages.drop past.length)

theorem response_steps_cons (kind : JointResponse.Kind) (trace : List JointResponse.Kind) :
    UnifiedResponseBudget.responseSteps (kind :: trace) =
      (if UnifiedResponseBudget.responseKind kind then 1 else 0) + UnifiedResponseBudget.responseSteps trace := by
  unfold UnifiedResponseBudget.responseSteps
  cases actual : UnifiedResponseBudget.responseKind kind <;> simp [actual, Nat.add_comm]

theorem every_original_run_pays_for_all_physical_signature_opportunities
    (rounds : Nat) (past : JointResponse.Stages model) :
    physical model start vocabulary encoding law rounds past ≤
      UnifiedResponseBudget.responseSteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace +
        CommunicationWorkBudget.retryCost model start vocabulary encoding law rounds past := by
  induction rounds generalizing past with
  | zero =>
    simp only [physical, JointResponseRun.run, CommunicationWorkBudget.retryCost]
    split
    · simp only [List.drop_length, tally, UnifiedResponseBudget.responseSteps, List.filter_nil, List.length_nil, Nat.le_refl]
    · split <;> simp only [List.drop_length, tally, UnifiedResponseBudget.responseSteps, List.filter_nil, List.length_nil, Nat.le_refl]
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [physical, JointResponseRun.run, CommunicationWorkBudget.retryCost, actual, List.drop_length, tally,
        UnifiedResponseBudget.responseSteps, List.filter_nil, List.length_nil, Nat.le_refl]
    | exhausted empty => simp only [physical, JointResponseRun.run, CommunicationWorkBudget.retryCost, actual, List.drop_length, tally,
        UnifiedResponseBudget.responseSteps, List.filter_nil, List.length_nil, Nat.le_refl]
    | advance action =>
      obtain ⟨more, afterExact⟩ := JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action
      obtain ⟨tail, finalExact⟩ := JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law rounds
        (JointResponse.after model start vocabulary encoding law past action)
      have paid := each_original_macro_pays_for_its_signature_opportunities model start vocabulary encoding law past more action actual afterExact
      have next := ih (JointResponse.after model start vocabulary encoding law past action)
      have suffix : physical model start vocabulary encoding law rounds (JointResponse.after model start vocabulary encoding law past action) =
          tally model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) tail := by
        unfold physical
        rw [← finalExact, List.drop_left]
      rw [suffix] at next
      simp only [physical, JointResponseRun.run, actual, CommunicationWorkBudget.retryCost, response_steps_cons]
      rw [← finalExact, ← afterExact, List.append_assoc, List.drop_left, tally_append, afterExact]
      omega

theorem the_original_source_bounds_all_signature_opportunities
    (rounds : Nat) (past : JointResponse.Stages model) (delayAllowance : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start delayAllowance
      (JointResponseRun.run model start vocabulary encoding law rounds past).stages) :
    physical model start vocabulary encoding law rounds past ≤ ForwardResponseBudget.allowance model start vocabulary encoding law past := by
  have physical := every_original_run_pays_for_all_physical_signature_opportunities model start vocabulary encoding law rounds past
  have responses := UnifiedResponseBudget.the_actual_joint_run_has_a_source_generated_response_execution_budget
    model start vocabulary encoding law rounds past delayAllowance compliant
  have retries := CommunicationWorkBudget.every_actual_retry_schedule_has_a_source_generated_total_cost
    model start vocabulary encoding law rounds past
  unfold ForwardResponseBudget.allowance UnifiedResponseBudget.remaining PhysicalOpportunityBudget.retrySlots
  omega

def Needed (past : JointResponse.Stages model) (receiver : Fin model.source.code.sites) : Prop :=
  ((UnifiedResponse.incidents model start vocabulary encoding law past).head?.map (fun head => head.receiver)) = some receiver ∨
    ResponseEligibility.pendingAt model start vocabulary encoding law past receiver ≠ []
instance (past : JointResponse.Stages model) (receiver : Fin model.source.code.sites) :
    Decidable (Needed model start vocabulary encoding law past receiver) := by unfold Needed; infer_instance

def Available (past more : JointResponse.Stages model) : Prop :=
  ∀ n : Fin more.length, ∀ receiver : Fin model.source.code.sites,
    Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start (past ++ more.take n.val)).ownerStart
      (EventStep.seed (EventHistory.execute start (past ++ more.take n.val))).history.length = some receiver →
    Needed model start vocabulary encoding law (past ++ more.take n.val) receiver →
    ResponseEligibility.Resources model start (past ++ more.take n.val) receiver
instance (past more : JointResponse.Stages model) : Decidable (Available model start vocabulary encoding law past more) := by
  unfold Available
  infer_instance

theorem availability_at_an_actual_initial_segment
    (past more : JointResponse.Stages model) (length : Nat)
    (available : Available model start vocabulary encoding law past more) :
    Available model start vocabulary encoding law past (more.take length) := by
  intro n receiver owned needed
  have bound : n.val < more.length ∧ n.val ≤ length := by
    have inside := n.isLt
    simp only [List.length_take] at inside
    omega
  have cut : (more.take length).take n.val = more.take n.val := by
    rw [List.take_take, Nat.min_eq_left bound.2]
  have actual := available ⟨n.val, bound.1⟩ receiver
  rw [cut] at owned needed ⊢
  exact actual owned needed

theorem availability_at_the_same_actual_remaining_segment
    (past more : JointResponse.Stages model) (length : Nat) (room : length ≤ more.length)
    (available : Available model start vocabulary encoding law past more) :
    Available model start vocabulary encoding law (past ++ more.take length) (more.drop length) := by
  intro n receiver owned needed
  have bound : length + n.val < more.length := by
    have inside := n.isLt
    simp only [List.length_drop] at inside
    omega
  have cut : past ++ more.take (length + n.val) = (past ++ more.take length) ++ (more.drop length).take n.val := by
    rw [List.take_add, List.append_assoc]
  have actual := available ⟨length + n.val, bound⟩ receiver
  rw [cut] at actual
  exact actual owned needed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureClock
