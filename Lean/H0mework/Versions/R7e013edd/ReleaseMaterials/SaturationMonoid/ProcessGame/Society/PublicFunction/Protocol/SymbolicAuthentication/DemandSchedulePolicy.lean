import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandSchedulePolicy
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open RecycledQuorumMaterial (Current)
open RenewedQuorumSource (fee)

def work (second : Bool) : code.Policy := fun key _ =>
  if key.1 = 2 then RenewedQuorumMaterial.word else [fee second]

theorem work_generated (second : Bool) : work second ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key inside
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split_ifs <;>
    simp [RenewedQuorumMaterial.word,
      RenewedQuorumMaterial.supply,RecycledQuorumMaterial.word]
  all_goals cases second <;> simp

def canSpend (current : Current) : Bool :=
  decide (1 ≤ current.stock 1 .service) || !DemandRenewalStep.refill current

-- This source dispatcher installs a generated Rule; it does not change Code.readLocal.
def compile (current : Current) (available second : Bool) : Rule code :=
  ⟨⟨work second,work_generated second⟩,fun key _ =>
    if key.1 = 2 then
      if available && DemandRenewalStep.refill current then
        RenewedQuorumSource.activation _ _ _ key.1 else ⟨none,List.mem_cons_self⟩
    else if canSpend current then RenewedQuorumSource.activation _ _ _ key.1
    else ⟨none,List.mem_cons_self⟩⟩

theorem every_installed_rule_is_in_the_original_source_domain
    (current : Current) (available second : Bool) : compile current available second ∈ rules code :=
  every_rule_is_source_generated code _

def payer (row : StageTrace.Record (code := code)) : Bool :=
  match StageTrace.activation row with
  | some site => decide (site ≠ 2)
  | none => false

-- A cached actual state avoids replaying the growing source inside each branch.
def materialAt (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (before : Feedback.State code) : StageTrace.Record (code := code) :=
  let call := StageTrace.capture cursor protocol rival before
  let selected : Input code := ⟨fun _ _ _ => ControlExecution.admitted code call,cursor.entry.budget⟩
  ⟨cursor,protocol,before,call,word code (some protocol.work.val) selected before,
    Reaction.Feedback.advance code (some protocol.work.val) selected before⟩

theorem cached_material_is_the_actual_occurrence
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (before : Feedback.State code) (correct : before = EventStep.seed cursor) :
    materialAt cursor protocol rival before = StageTrace.material cursor protocol rival := by
  subst before
  rfl

theorem cached_after_is_the_same_source_successor
    (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (before : Feedback.State code) (correct : before = EventStep.seed cursor) :
    (materialAt cursor protocol rival before).after = EventStep.seed (cursor.after protocol rival) := by
  rw [cached_material_is_the_actual_occurrence cursor protocol rival before correct]
  exact (StageTrace.material_is_the_actual_step cursor protocol rival).1

theorem every_payer_activation_submits_the_original_fee
    (cursor : Cursor code) (available second : Bool) (rival : Opponent code)
    (actual : payer (StageTrace.material cursor (compile (EventStep.seed cursor).current available second) rival) = true) :
    (StageTrace.material cursor (compile (EventStep.seed cursor).current available second) rival).submitted = [fee second] := by
  unfold payer at actual
  cases activated : StageTrace.activation (StageTrace.material cursor (compile (EventStep.seed cursor).current available second) rival) with
  | none => simp only [activated] at actual; contradiction
  | some site =>
    simp only [activated,decide_eq_true_eq] at actual
    have selected := (StageTrace.an_owned_activation_submits_its_selected_work cursor
      (compile (EventStep.seed cursor).current available second) rival site activated).2
    rw [selected]
    simp [Distributed.Code.action,compile,work,actual,code,RenewedQuorumSource.code]

theorem cached_payer_submits_the_original_fee
    (cursor : Cursor code) (before : Feedback.State code) (correct : before = EventStep.seed cursor)
    (available second : Bool) (rival : Opponent code)
    (actual : payer (materialAt cursor (compile before.current available second) rival before) = true) :
    (materialAt cursor (compile before.current available second) rival before).submitted = [fee second] := by
  subst before
  exact every_payer_activation_submits_the_original_fee cursor available second rival actual

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandSchedulePolicy
