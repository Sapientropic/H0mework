import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InventoryProgressConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionService
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedResponseBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityOpportunity
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

def offered (past : JointResponse.Stages model) : Bool :=
  !(UnifiedResponse.rejections model start vocabulary encoding law past).isEmpty &&
    match RejectionResponse.produce model start past vocabulary encoding law with
    | .ready _ => true
    | _ => false

def conflictKind : JointResponse.Kind → Bool
  | .communication .conflict => true
  | _ => false
def rejectionKind : JointResponse.Kind → Bool
  | .communication .rejection => true
  | _ => false
abbrev count (past : JointResponse.Stages model) :=
  (IncidentResponse.journal model start past vocabulary encoding law).length

theorem an_actual_local_offer_is_executed_or_spends_a_higher_priority_identity
    (past : JointResponse.Stages model) (available : offered model start vocabulary encoding law past = true) :
    ∃ action, JointResponse.step model start vocabulary encoding law past = .advance action ∧
      (conflictKind (JointResponse.kind model start vocabulary encoding law action) = true ∨
        rejectionKind (JointResponse.kind model start vocabulary encoding law action) = true) := by
  have pending : UnifiedResponse.rejections model start vocabulary encoding law past ≠ [] := by
    intro empty
    unfold offered at available
    rw [empty] at available
    simp at available
  have ready : ∃ response, RejectionResponse.produce model start past vocabulary encoding law = .ready response := by
    unfold offered at available
    cases selected : RejectionResponse.produce model start past vocabulary encoding law <;> simp_all
  obtain ⟨response, selected⟩ := ready
  have live : 0 < JointResponse.fuel model start past := response.fuel
  have notUnified : ¬ UnifiedResponse.Clear model start vocabulary encoding law past := fun clear => pending clear.2.1
  have notJoint : ¬ JointResponse.Clear model start vocabulary encoding law past := fun clear => notUnified clear.1
  have unified : ∃ action : UnifiedResponse.Action model start vocabulary encoding law past,
      UnifiedResponse.step model start vocabulary encoding law past = .advance action ∧
      (conflictKind (JointResponse.kind model start vocabulary encoding law (.communication action)) = true ∨
        rejectionKind (JointResponse.kind model start vocabulary encoding law (.communication action)) = true) := by
    unfold UnifiedResponse.step
    rw [dif_neg notUnified, dif_pos live]
    split
    · rename_i answer actualConflict
      exact ⟨.conflict answer actualConflict, rfl, Or.inl rfl⟩
    all_goals
      split
      · rename_i answer actualRejection
        exact ⟨.rejection answer actualRejection, rfl, Or.inr rfl⟩
      all_goals simp_all
  obtain ⟨action, chosen, priority⟩ := unified
  refine ⟨.communication action, ?_, priority⟩
  simp only [JointResponse.step, dif_neg notJoint, dif_pos live, chosen]

theorem every_actual_conflict_spends_a_distinct_original_identity
    (past : JointResponse.Stages model) (action : JointResponse.Action model start vocabulary encoding law past)
    (conflict : conflictKind (JointResponse.kind model start vocabulary encoding law action) = true) :
    count model start vocabulary encoding law (JointResponse.after model start vocabulary encoding law past action) =
      count model start vocabulary encoding law past + 1 := by
  cases action with
  | communication action =>
    cases action with
    | conflict response selected =>
      have grew := congrArg List.length (IncidentResponse.a_generated_response_is_registered_once
        model start past vocabulary encoding law response (OriginQueue.environment start) selected)
      simpa only [count, JointResponse.after, UnifiedResponse.after, List.length_map,
        List.length_append, List.length_singleton] using grew
    | rejection response selected => contradiction
    | retry response selected => contradiction
    | wait live => contradiction
  | withdrawal ready accepted selected => contradiction
  | refused ready denied selected => contradiction
  | wait live => contradiction

theorem actual_extension_preserves_the_priority_identity_count
    (past later : JointResponse.Stages model) (ordered : past <+: later) :
    count model start vocabulary encoding law past ≤ count model start vocabulary encoding law later :=
  (UnifiedResponseBudget.actual_extension_preserves_both_original_journals model start vocabulary encoding law past later ordered).1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityOpportunity
