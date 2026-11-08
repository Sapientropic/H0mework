import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PriorityServiceConsumer
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseEligibility
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open private planAt from H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

def pendingAt (past : JointResponse.Stages model) (receiver : Fin model.source.code.sites) :=
  (RejectionResponse.observed model start past vocabulary encoding law receiver).filter fun evidence =>
    decide ((receiver, evidence.index) ∉ (RejectionResponse.journal model start past vocabulary encoding law).map
      (RejectionResponse.Answer.id model start vocabulary encoding law))

def Resources (past : JointResponse.Stages model) (receiver : Fin model.source.code.sites) : Prop :=
  RejectionResponse.signature model receiver ∈ model.source.code.actions ∧
  1 ≤ model.source.code.actionLimit ∧ Event.activate receiver ∈ model.source.code.eventAlphabet ∧
  0 < JointResponse.fuel model start past ∧
  model.source.code.memoryReady ((EventStep.seed (EventHistory.execute start past)).frame.inbox receiver) = true ∧
  Mandate.Challenge.Submission (scope := model.scope) (RejectionResponse.signature model receiver) ∧
  model.source.code.law.Valid (EventStep.seed (EventHistory.execute start past)).current (RejectionResponse.signature model receiver) ∧
  RejectionResponse.Active model start past
instance (past : JointResponse.Stages model) (receiver : Fin model.source.code.sites) :
    Decidable (Resources model start past receiver) := by unfold Resources; infer_instance

-- This guard reads primitive source state and the original unhandled evidence, not Ready.
def eligible (past : JointResponse.Stages model) : Bool :=
  match Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length with
  | none => false
  | some receiver => !(pendingAt model start vocabulary encoding law past receiver).isEmpty &&
      decide (Resources model start past receiver)

theorem actual_source_resources_and_unhandled_evidence_generate_the_original_ready
    (past : JointResponse.Stages model) (receiver : Fin model.source.code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length = some receiver)
    (pending : pendingAt model start vocabulary encoding law past receiver ≠ [])
    (resources : Resources model start past receiver) :
    ∃ response, RejectionResponse.produce model start past vocabulary encoding law = .ready response := by
  rcases resources with ⟨supported, capacity, activation, fuel, memory, standing, valid, active⟩
  have first : ∃ evidence, (pendingAt model start vocabulary encoding law past receiver).head? = some evidence := by
    cases actual : pendingAt model start vocabulary encoding law past receiver with
    | nil => exact False.elim (pending actual)
    | cons head tail => exact ⟨head, rfl⟩
  obtain ⟨evidence, first⟩ := first
  unfold pendingAt at first
  unfold RejectionResponse.produce planAt
  split
  · rename_i noOwner
    rw [owned] at noOwner
    cases noOwner
  · rename_i worker owner
    have same : worker = receiver := Option.some.inj (owner.symm.trans owned)
    subst worker
    split
    · rename_i noEvidence
      rw [noEvidence] at first
      cases first
    · repeat' first | split | contradiction
      exact ⟨_, rfl⟩

theorem an_actual_primitive_eligible_cut_generates_a_priority_offer
    (past : JointResponse.Stages model) (actual : eligible model start vocabulary encoding law past = true) :
    PriorityOpportunity.offered model start vocabulary encoding law past = true := by
  unfold eligible at actual
  split at actual
  · contradiction
  · rename_i receiver owned
    have resource : Resources model start past receiver := of_decide_eq_true (Bool.and_eq_true_iff.mp actual).2
    have pending : pendingAt model start vocabulary encoding law past receiver ≠ [] := by
      intro empty
      simp only [empty, List.isEmpty_nil, Bool.not_true, Bool.false_and, Bool.false_eq_true] at actual
    obtain ⟨response, selected⟩ := actual_source_resources_and_unhandled_evidence_generate_the_original_ready
      model start vocabulary encoding law past receiver owned pending resource
    have nonempty : UnifiedResponse.rejections model start vocabulary encoding law past ≠ [] := by
      cases found : pendingAt model start vocabulary encoding law past receiver with
      | nil => exact False.elim (pending found)
      | cons head tail =>
        have member : head ∈ pendingAt model start vocabulary encoding law past receiver := found ▸ List.mem_cons_self
        obtain ⟨observed, fresh⟩ := List.mem_filter.mp member
        have identity : (receiver, head.index) ∈ UnifiedResponse.rejections model start vocabulary encoding law past :=
          List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨receiver, List.mem_finRange _,
            List.mem_map.mpr ⟨head, observed, rfl⟩⟩, fresh⟩
        intro empty
        rw [empty] at identity
        contradiction
    simp only [PriorityOpportunity.offered, selected, Bool.and_true, Bool.not_eq_true']
    simpa only [List.isEmpty_eq_false_iff] using nonempty

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResponseEligibility
