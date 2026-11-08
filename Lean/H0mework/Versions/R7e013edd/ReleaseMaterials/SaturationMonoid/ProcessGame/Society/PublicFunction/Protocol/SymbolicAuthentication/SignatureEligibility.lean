import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseConsumer
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureEligibility
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

def incident (past : JointResponse.Stages model) : Bool :=
  match (UnifiedResponse.incidents model start vocabulary encoding law past).head? with
  | none => false
  | some head => decide (
      Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
        (EventStep.seed (EventHistory.execute start past)).history.length = some head.receiver ∧
      ResponseEligibility.Resources model start past head.receiver)

def eligible (past : JointResponse.Stages model) :=
  incident model start vocabulary encoding law past || ResponseEligibility.eligible model start vocabulary encoding law past

def Clear (past : JointResponse.Stages model) : Prop :=
  UnifiedResponse.incidents model start vocabulary encoding law past = [] ∧
    UnifiedResponse.rejections model start vocabulary encoding law past = []
instance (past : JointResponse.Stages model) : Decidable (Clear model start vocabulary encoding law past) := by
  unfold Clear
  infer_instance

namespace Incident
open private planAt from H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponse

theorem primitive_head_resources_generate_the_original_incident_response
    (past : JointResponse.Stages model)
    (head : StageAccountability.Incident start vocabulary encoding law)
    (first : (UnifiedResponse.incidents model start vocabulary encoding law past).head? = some head)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length = some head.receiver)
    (resources : ResponseEligibility.Resources model start past head.receiver) :
    ∃ response, IncidentResponse.produce model start past vocabulary encoding law = .ready response := by
  rcases resources with ⟨supported, capacity, activation, fuel, memory, standing, valid, active⟩
  unfold UnifiedResponse.incidents ResponseSweep.unhandled at first
  unfold IncidentResponse.produce planAt
  split
  · rename_i absent
    rw [absent] at first
    cases first
  · rename_i selected found
    have same : selected = head := Option.some.inj (found.symm.trans first)
    subst selected
    repeat' first | split | contradiction
    exact ⟨_, rfl⟩

theorem actual_ready_is_primitive
    (past : JointResponse.Stages model) (response : IncidentResponse.Ready model start past vocabulary encoding law)
    (selected : IncidentResponse.produce model start past vocabulary encoding law = .ready response) :
    incident model start vocabulary encoding law past = true := by
  unfold IncidentResponse.produce planAt at selected
  split at selected
  · split at selected <;> contradiction
  · rename_i head first
    repeat' first | split at selected | contradiction
    unfold incident UnifiedResponse.incidents ResponseSweep.unhandled
    rw [first]
    exact decide_eq_true ⟨by assumption, by exact ⟨by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption⟩⟩

end Incident

namespace Rejection
open private planAt from H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse

theorem actual_ready_is_primitive
    (past : JointResponse.Stages model) (response : RejectionResponse.Ready model start past vocabulary encoding law)
    (selected : RejectionResponse.produce model start past vocabulary encoding law = .ready response) :
    ResponseEligibility.eligible model start vocabulary encoding law past = true := by
  unfold RejectionResponse.produce planAt at selected
  split at selected
  · contradiction
  · rename_i receiver owner
    split at selected
    · contradiction
    · rename_i evidence first
      repeat' first | split at selected | contradiction
      have pending : ResponseEligibility.pendingAt model start vocabulary encoding law past receiver ≠ [] := by
        intro empty
        change (ResponseEligibility.pendingAt model start vocabulary encoding law past receiver).head? = some evidence at first
        rw [empty] at first
        cases first
      simp only [ResponseEligibility.eligible, owner, Bool.and_eq_true_iff, decide_eq_true_eq]
      exact ⟨by simpa only [Bool.not_eq_true', List.isEmpty_eq_false_iff] using pending,
        ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
          by assumption, by assumption⟩⟩

end Rejection

theorem priority_kind_is_response (kind : JointResponse.Kind)
    (priority : PriorityOpportunity.conflictKind kind = true ∨ PriorityOpportunity.rejectionKind kind = true) :
    UnifiedResponseBudget.responseKind kind = true := by
  cases kind with
  | communication kind => cases kind <;> simp_all [PriorityOpportunity.conflictKind, PriorityOpportunity.rejectionKind, UnifiedResponseBudget.responseKind]
  | withdrawal | refused | wait => simp_all [PriorityOpportunity.conflictKind, PriorityOpportunity.rejectionKind]

theorem a_primitive_signature_opportunity_selects_an_original_response_action
    (past : JointResponse.Stages model) (actual : eligible model start vocabulary encoding law past = true) :
    ∃ action, JointResponse.step model start vocabulary encoding law past = .advance action ∧
      UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law action) = true := by
  rcases Bool.or_eq_true_iff.mp actual with headReady | rejectionReady
  · have ready : ∃ response, IncidentResponse.produce model start past vocabulary encoding law = .ready response := by
      unfold incident at headReady
      split at headReady
      · contradiction
      · rename_i head first
        obtain ⟨owned, resources⟩ := of_decide_eq_true headReady
        exact Incident.primitive_head_resources_generate_the_original_incident_response
          model start vocabulary encoding law past head first owned resources
    obtain ⟨response, selected⟩ := ready
    have pending : UnifiedResponse.incidents model start vocabulary encoding law past ≠ [] := by
      intro empty
      unfold incident at headReady
      rw [empty] at headReady
      contradiction
    have notUnified : ¬ UnifiedResponse.Clear model start vocabulary encoding law past := fun covered => pending covered.1
    have notJoint : ¬ JointResponse.Clear model start vocabulary encoding law past := fun covered => notUnified covered.1
    have live : 0 < JointResponse.fuel model start past := response.fuel
    have unified : ∃ action : UnifiedResponse.Action model start vocabulary encoding law past,
        UnifiedResponse.step model start vocabulary encoding law past = .advance action ∧
        UnifiedResponseBudget.responseKind (JointResponse.kind model start vocabulary encoding law (.communication action)) = true := by
      unfold UnifiedResponse.step
      rw [dif_neg notUnified, dif_pos live]
      split
      · exact ⟨_, rfl, rfl⟩
      all_goals simp_all
    obtain ⟨action, chosen, kind⟩ := unified
    refine ⟨.communication action, ?_, kind⟩
    simp only [JointResponse.step, dif_neg notJoint, dif_pos live, chosen]
  · have offered := ResponseEligibility.an_actual_primitive_eligible_cut_generates_a_priority_offer
      model start vocabulary encoding law past rejectionReady
    obtain ⟨action, selected, kind⟩ := PriorityOpportunity.an_actual_local_offer_is_executed_or_spends_a_higher_priority_identity
      model start vocabulary encoding law past offered
    exact ⟨action, selected, priority_kind_is_response _ kind⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureEligibility
