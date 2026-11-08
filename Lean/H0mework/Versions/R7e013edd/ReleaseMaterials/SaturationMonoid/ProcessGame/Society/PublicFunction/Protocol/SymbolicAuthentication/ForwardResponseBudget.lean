import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseClock

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseBudget
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

theorem every_actual_dispatch_offer_is_paid_by_a_joint_response
    (rounds : Nat) (past : JointResponse.Stages model) :
    PriorityServiceTrace.offers model start vocabulary encoding law rounds past ≤
      UnifiedResponseBudget.responseSteps (JointResponseRun.run model start vocabulary encoding law rounds past).trace := by
  induction rounds generalizing past with
  | zero =>
    simp only [PriorityServiceTrace.offers, JointResponseRun.run]
    split
    · exact Nat.zero_le _
    · split <;> exact Nat.zero_le _
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [PriorityServiceTrace.offers, actual]; exact Nat.zero_le _
    | exhausted empty => simp only [PriorityServiceTrace.offers, actual]; exact Nat.zero_le _
    | advance action =>
      have next := ih (JointResponse.after model start vocabulary encoding law past action)
      simp only [PriorityServiceTrace.offers, JointResponseRun.run, actual,
        UnifiedResponseBudget.responseSteps, List.filter_cons]
      by_cases offered : PriorityOpportunity.offered model start vocabulary encoding law past = true
      · obtain ⟨chosen, selected, kind⟩ :=
          PriorityOpportunity.an_actual_local_offer_is_executed_or_spends_a_higher_priority_identity
            model start vocabulary encoding law past offered
        have same := JointResponse.Step.advance.inj (selected.symm.trans actual)
        subst chosen
        have response : UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) = true := by
          cases kind with
          | inl conflict =>
            cases actualKind : JointResponse.kind model start vocabulary encoding law action <;>
              simp_all [PriorityOpportunity.conflictKind, UnifiedResponseBudget.responseKind]
            all_goals split at conflict <;> simp_all
          | inr rejected =>
            cases actualKind : JointResponse.kind model start vocabulary encoding law action <;>
              simp_all [PriorityOpportunity.rejectionKind, UnifiedResponseBudget.responseKind]
            all_goals split at rejected <;> simp_all
        simp only [offered, response, if_true, List.length_cons]
        unfold UnifiedResponseBudget.responseSteps at next
        omega
      · rw [if_neg offered]
        unfold UnifiedResponseBudget.responseSteps at next
        split <;> simp only [List.length_cons, Nat.zero_add] <;> omega

def allowance (past : JointResponse.Stages model) :=
  UnifiedResponseBudget.remaining model start vocabulary encoding law past + PhysicalOpportunityBudget.retrySlots model start

def deadline (past : JointResponse.Stages model) :=
  ForwardResponseClock.width model start * (allowance model start vocabulary encoding law past + 1)

theorem every_compliant_actual_run_has_a_source_generated_physical_opportunity_budget
    (rounds : Nat) (past : JointResponse.Stages model) (birthAllowance : Nat)
    (compliant : AdaptiveRejectionHistory.Compliant start birthAllowance
      (JointResponseRun.run model start vocabulary encoding law rounds past).stages) :
    PhysicalOpportunityClock.physical model start vocabulary encoding law rounds past ≤
      allowance model start vocabulary encoding law past := by
  have physical := PhysicalOpportunityBudget.all_actual_physical_opportunities_are_dispatch_offers_or_paid_retry_slots
    model start vocabulary encoding law rounds past
  have offers := every_actual_dispatch_offer_is_paid_by_a_joint_response model start vocabulary encoding law rounds past
  have responses := UnifiedResponseBudget.the_actual_joint_run_has_a_source_generated_response_execution_budget
    model start vocabulary encoding law rounds past birthAllowance compliant
  have retries := CommunicationWorkBudget.every_actual_retry_schedule_has_a_source_generated_total_cost
    model start vocabulary encoding law rounds past
  unfold allowance UnifiedResponseBudget.remaining PhysicalOpportunityBudget.retrySlots
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseBudget
