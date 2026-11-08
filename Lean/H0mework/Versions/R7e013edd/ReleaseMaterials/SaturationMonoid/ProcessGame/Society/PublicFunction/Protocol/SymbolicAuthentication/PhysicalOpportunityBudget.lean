import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityClock

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityBudget
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open PhysicalOpportunityClock

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem all_actual_physical_opportunities_are_dispatch_offers_or_paid_retry_slots
    (rounds : Nat) (past : JointResponse.Stages model) :
    physical model start vocabulary encoding law rounds past ≤
      PriorityServiceTrace.offers model start vocabulary encoding law rounds past +
        CommunicationWorkBudget.retryCost model start vocabulary encoding law rounds past := by
  induction rounds generalizing past with
  | zero =>
    simp only [physical, JointResponseRun.run, PriorityServiceTrace.offers, CommunicationWorkBudget.retryCost]
    split
    · simp only [List.drop_length, tally, Nat.le_refl]
    · split <;> simp only [List.drop_length, tally, Nat.le_refl]
  | succ rounds ih =>
    cases actual : JointResponse.step model start vocabulary encoding law past with
    | clear closed => simp only [physical, JointResponseRun.run, PriorityServiceTrace.offers, CommunicationWorkBudget.retryCost, actual, List.drop_length, tally, Nat.le_refl]
    | exhausted empty => simp only [physical, JointResponseRun.run, PriorityServiceTrace.offers, CommunicationWorkBudget.retryCost, actual, List.drop_length, tally, Nat.le_refl]
    | advance action =>
      obtain ⟨more, afterExact⟩ := JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action
      obtain ⟨tail, finalExact⟩ := JointResponseRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law rounds
        (JointResponse.after model start vocabulary encoding law past action)
      have paid := an_actual_macro_charges_nondispatch_opportunities_to_its_own_retry_length model start vocabulary encoding law past more action afterExact
      have next := ih (JointResponse.after model start vocabulary encoding law past action)
      have suffix : physical model start vocabulary encoding law rounds
          (JointResponse.after model start vocabulary encoding law past action) =
          tally model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) tail := by
        unfold physical
        rw [← finalExact, List.drop_left]
      rw [suffix] at next
      simp only [physical, JointResponseRun.run, PriorityServiceTrace.offers, CommunicationWorkBudget.retryCost, actual]
      rw [← finalExact, ← afterExact, List.append_assoc, List.drop_left, tally_append, afterExact]
      omega

def retrySlots := RetryProgress.capacity (code := model.source.code) * CommunicationWorkBudget.slotAllowance model start
def remaining (past : JointResponse.Stages model) :=
  IncidentInventory.capacity (code := model.source.code) - PriorityOpportunity.count model start vocabulary encoding law past + retrySlots model start

theorem no_selected_rejection_edge_has_a_source_generated_physical_opportunity_bound
    (rounds : Nat) (past : JointResponse.Stages model)
    (absent : PriorityServiceTrace.first model start vocabulary encoding law rounds past = none) :
    physical model start vocabulary encoding law rounds past ≤ remaining model start vocabulary encoding law past := by
  have deferred := PriorityServiceTrace.absent_service_charges_every_actual_offer_to_a_priority_identity model start vocabulary encoding law rounds past absent
  have incidentBound := IncidentRegistration.the_number_of_actual_native_responses_has_the_original_source_budget
    model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages
  have physicalBound := all_actual_physical_opportunities_are_dispatch_offers_or_paid_retry_slots model start vocabulary encoding law rounds past
  have slots := CommunicationWorkBudget.every_actual_retry_schedule_has_a_source_generated_total_cost model start vocabulary encoding law rounds past
  change PriorityOpportunity.count model start vocabulary encoding law _ ≤ _ at incidentBound
  unfold remaining retrySlots
  omega

theorem enough_actual_primitive_physical_opportunities_generate_an_actual_service
    (rounds : Nat) (past : JointResponse.Stages model)
    (enough : remaining model start vocabulary encoding law past < physical model start vocabulary encoding law rounds past) :
    ∃ n, PriorityServiceTrace.first model start vocabulary encoding law rounds past = some n ∧
      past.length ≤ n ∧ n < (JointResponseRun.run model start vocabulary encoding law rounds past).stages.length ∧
      RejectionService.ServedAt model start vocabulary encoding law (JointResponseRun.run model start vocabulary encoding law rounds past).stages n := by
  cases selected : PriorityServiceTrace.first model start vocabulary encoding law rounds past with
  | some n => exact ⟨n, rfl, PriorityServiceTrace.the_first_source_selected_service_is_an_actual_row model start vocabulary encoding law rounds past n selected⟩
  | none =>
    have bounded := no_selected_rejection_edge_has_a_source_generated_physical_opportunity_bound model start vocabulary encoding law rounds past selected
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityBudget
