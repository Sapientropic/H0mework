import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeReviewRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponse

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
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

abbrev Stages := UnifiedResponse.Stages model
abbrev fuel := UnifiedResponse.fuel model start

abbrev current (past : Stages model) := EventStep.seed (EventHistory.execute start past)
def queueClear (past : Stages model) : Bool :=
  (OriginQueue.environment start (current model start past).history
    (current model start past).past (current model start past).frame).isNone

def Clear (past : Stages model) : Prop :=
  UnifiedResponse.Clear model start vocabulary encoding law past ∧
    NativeReview.complete model start past = true ∧ queueClear model start past = true
instance (past : Stages model) : Decidable (Clear model start vocabulary encoding law past) := by
  unfold Clear; infer_instance

inductive Action (past : Stages model) where
  | communication (action : UnifiedResponse.Action model start vocabulary encoding law past)
  | withdrawal (ready : NativeReview.Ready model start past)
      (accepted : model.source.code.law.Valid (EventStep.seed (NativeReview.current model start past)).current
        (NativeReview.action model start past ready.receiver))
      (selected : NativeReview.produce model start past = .paid ready accepted)
  | refused (ready : NativeReview.Ready model start past)
      (denied : ¬ model.source.code.law.Valid (EventStep.seed (NativeReview.current model start past)).current
        (NativeReview.action model start past ready.receiver))
      (selected : NativeReview.produce model start past = .refused ready denied)
  | wait (live : 0 < fuel model start past)

inductive Kind where
  | communication (kind : UnifiedResponse.Kind)
  | withdrawal | refused | wait
  deriving DecidableEq

def kind {past : Stages model} : Action model start vocabulary encoding law past → Kind
  | .communication action => .communication (UnifiedResponse.kind model start vocabulary encoding law action)
  | .withdrawal .. => .withdrawal
  | .refused .. => .refused
  | .wait _ => .wait

def after (past : Stages model) : Action model start vocabulary encoding law past → Stages model
  | .communication action => UnifiedResponse.after model start vocabulary encoding law past action
  | .withdrawal ready .. | .refused ready .. =>
      past ++ [(NativeReview.protocol model start past ready, OriginQueue.environment start)]
  | .wait _ => past ++ [(SilentWindow.quiet, OriginQueue.environment start)]

inductive Step (past : Stages model) where
  | clear (covered : Clear model start vocabulary encoding law past)
  | exhausted (empty : fuel model start past = 0)
  | advance (action : Action model start vocabulary encoding law past)

-- A newly arrived communication obligation takes priority over another native attempt.
-- Every successor re-enters this same gate, including paid and refused successors.
def step (past : Stages model) : Step model start vocabulary encoding law past :=
  if covered : Clear model start vocabulary encoding law past then .clear covered
  else if live : 0 < fuel model start past then
    match UnifiedResponse.step model start vocabulary encoding law past with
    | .advance action => .advance (.communication action)
    | .exhausted empty => .exhausted empty
    | .clear responses =>
      if quiet : queueClear model start past = true then
        match selected : NativeReview.produce model start past with
        | .clear closed => .clear ⟨responses, closed, quiet⟩
        | .paid ready accepted => .advance (.withdrawal ready accepted selected)
        | .refused ready denied => .advance (.refused ready denied selected)
        | _ => .advance (.wait live)
      else .advance (.wait live)
  else .exhausted (by omega)

theorem every_action_retains_the_whole_actual_prefix (past : Stages model)
    (action : Action model start vocabulary encoding law past) :
    past <+: after model start vocabulary encoding law past action := by
  cases action with
  | communication action => exact UnifiedResponse.every_action_retains_the_actual_prefix model start vocabulary encoding law past action
  | withdrawal ready accepted selected => exact List.prefix_append _ _
  | refused ready denied selected => exact List.prefix_append _ _
  | wait live => exact List.prefix_append _ _

theorem every_action_spends_actual_fuel (past : Stages model)
    (action : Action model start vocabulary encoding law past) :
    fuel model start (after model start vocabulary encoding law past action) < fuel model start past := by
  cases action with
  | communication action => exact UnifiedResponse.every_action_spends_actual_fuel model start vocabulary encoding law past action
  | withdrawal ready accepted selected =>
    change fuel model start (past ++ [_]) < _
    simp only [fuel, UnifiedResponse.fuel_after_actual_extension, List.length_singleton]
    have positive := ready.fuel
    change 0 < UnifiedResponse.fuel model start past at positive
    omega
  | refused ready denied selected =>
    change fuel model start (past ++ [_]) < _
    simp only [fuel, UnifiedResponse.fuel_after_actual_extension, List.length_singleton]
    have positive := ready.fuel
    change 0 < UnifiedResponse.fuel model start past at positive
    omega
  | wait live =>
    change fuel model start (past ++ [_]) < _
    simp only [fuel, UnifiedResponse.fuel_after_actual_extension, List.length_singleton]
    change 0 < UnifiedResponse.fuel model start past at live
    omega

theorem completion_consumes_every_actual_communication_and_original_claim (past : Stages model)
    (covered : Clear model start vocabulary encoding law past) :
    (∀ incident ∈ StageAccountability.ledger start vocabulary encoding law past,
      IncidentResponse.identity model start vocabulary encoding law incident ∈
        (IncidentResponse.journal model start past vocabulary encoding law).map (IncidentResponse.Answer.id model start vocabulary encoding law)) ∧
    (∀ receiver, ∀ evidence ∈ ReceptionEvidence.observed start past vocabulary encoding law receiver,
      (receiver, evidence.index) ∈ (RejectionResponse.journal model start past vocabulary encoding law).map
        (RejectionResponse.Answer.id model start vocabulary encoding law)) ∧
    (∀ row ∈ StageDuty.histories start vocabulary encoding law past, row.2.2.state.TerminalAt 0) ∧
    (∀ original ∈ NativeReview.inventory model start past,
      original.2.isPending (NativeReview.family model start past) (NativeReview.sourceIndex model start past) = false) :=
  ⟨UnifiedResponse.clear_covers_every_actual_incident model start vocabulary encoding law past covered.1,
    UnifiedResponse.clear_covers_every_actual_rejection model start vocabulary encoding law past covered.1,
    UnifiedResponse.clear_covers_every_original_duty model start vocabulary encoding law past covered.1,
    (NativeReview.completion_covers_every_native_original model start past).mp covered.2.1⟩

theorem completion_has_no_unattempted_admitted_actual_packet (past : Stages model)
    (covered : Clear model start vocabulary encoding law past) (serial : Nat)
    (present : serial < (current model start past).frame.sent.length)
    (admitted : serial ∈ QueueScheduler.admitted model.source.code) :
    serial ∈ QueueScheduler.attempted model.source.code (OriginQueue.baseline start) (current model start past).past := by
  by_contra absent
  have pending : serial ∈ QueueScheduler.untried model.source.code (OriginQueue.baseline start) (current model start past).past :=
    Finset.mem_sdiff.mpr ⟨admitted, absent⟩
  obtain ⟨event, chosen⟩ := QueueScheduler.a_pending_admitted_packet_generates_a_move model.source.code
    (OriginQueue.baseline start) (current model start past).history (current model start past).past
    (current model start past).frame serial present pending
  have quiet := covered.2.2
  change (QueueScheduler.opponent model.source.code (OriginQueue.baseline start)
    (current model start past).history (current model start past).past (current model start past).frame).isNone = true at quiet
  rw [chosen] at quiet
  cases quiet

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointResponse
