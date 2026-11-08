import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SignatureHandoff

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryDispatch
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

abbrev Stages := JointResponse.Stages model
inductive Action (past : Stages model) where
  | original (action : JointResponse.Action model start vocabulary encoding law past)
  | recovery (answer : NativeRecovery.Ready model start past vocabulary encoding law)

inductive Kind where
  | original (kind : JointResponse.Kind)
  | recovery
  deriving DecidableEq

def kind {past : Stages model} : Action model start vocabulary encoding law past → Kind
  | .original action => .original (JointResponse.kind model start vocabulary encoding law action)
  | .recovery _ => .recovery

def after (past : Stages model) : Action model start vocabulary encoding law past → Stages model
  | .original action => JointResponse.after model start vocabulary encoding law past action
  | .recovery answer => NativeRecovery.full model start past vocabulary encoding law answer

inductive Step (past : Stages model) where
  | clear (complete : JointResponse.Clear model start vocabulary encoding law past)
  | exhausted (empty : JointResponse.fuel model start past = 0)
  | advance (action : Action model start vocabulary encoding law past)

def original (past : Stages model) : Step model start vocabulary encoding law past :=
  match JointResponse.step model start vocabulary encoding law past with
  | .clear complete => .clear complete
  | .exhausted empty => .exhausted empty
  | .advance action => .advance (.original action)

-- NativeRecovery itself checks complete communication, queue, local evidence and actual payment.
-- Every blocked recovery preserves the original dispatch, including legitimate fresh withdrawals.
def step (past : Stages model) : Step model start vocabulary encoding law past :=
  if complete : JointResponse.Clear model start vocabulary encoding law past then .clear complete
  else if 2 ≤ model.source.code.actionLimit then
    match NativeRecovery.produce model start past vocabulary encoding law with
    | .ready answer => .advance (.recovery answer)
    | .blocked _ => original model start vocabulary encoding law past
  else original model start vocabulary encoding law past

theorem every_action_keeps_the_whole_actual_history
    (past : Stages model) (action : Action model start vocabulary encoding law past) :
    past <+: after model start vocabulary encoding law past action := by
  cases action with
  | original action => exact JointResponse.every_action_retains_the_whole_actual_prefix model start vocabulary encoding law past action
  | recovery answer => exact NativeRecoveryMaterial.actual_recovery_preserves_the_complete_original_prefix model start past answer.material

theorem every_action_strictly_spends_the_same_source_fuel
    (past : Stages model) (action : Action model start vocabulary encoding law past) :
    JointResponse.fuel model start (after model start vocabulary encoding law past action) < JointResponse.fuel model start past := by
  cases action with
  | original action => exact JointResponse.every_action_spends_actual_fuel model start vocabulary encoding law past action
  | recovery answer =>
    have spent := UnifiedResponse.fuel_after_actual_extension model start past
      [(NativeRecoveryMaterial.protocol model start past answer.material, OriginQueue.environment start)]
    change JointResponse.fuel model start (after model start vocabulary encoding law past (.recovery answer)) =
      JointResponse.fuel model start past - 1 at spent
    have live := answer.material.live
    change 0 < JointResponse.fuel model start past at live
    omega

theorem a_blocked_recovery_retains_the_exact_original_dispatch
    (past : Stages model) (pending : ¬ JointResponse.Clear model start vocabulary encoding law past)
    (reason : NativeRecovery.Obstruction)
    (blocked : NativeRecovery.produce model start past vocabulary encoding law = .blocked reason) :
    step model start vocabulary encoding law past = original model start vocabulary encoding law past := by
  simp only [step, dif_neg pending, blocked]
  split <;> rfl

theorem an_actual_native_recovery_is_never_lost_to_the_capacity_precheck
    (past : Stages model) (pending : ¬ JointResponse.Clear model start vocabulary encoding law past)
    (answer : NativeRecovery.Ready model start past vocabulary encoding law)
    (selected : NativeRecovery.produce model start past vocabulary encoding law = .ready answer) :
    step model start vocabulary encoding law past = .advance (.recovery answer) := by
  simp only [step, dif_neg pending, if_pos answer.material.capacity, selected]

theorem every_selected_recovery_waits_for_the_original_communication_and_queue_gates
    (past : Stages model) (answer : NativeRecovery.Ready model start past vocabulary encoding law) :
    UnifiedResponse.Clear model start vocabulary encoding law past ∧ JointResponse.queueClear model start past = true :=
  ⟨answer.communication, answer.queue⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedRecoveryDispatch
