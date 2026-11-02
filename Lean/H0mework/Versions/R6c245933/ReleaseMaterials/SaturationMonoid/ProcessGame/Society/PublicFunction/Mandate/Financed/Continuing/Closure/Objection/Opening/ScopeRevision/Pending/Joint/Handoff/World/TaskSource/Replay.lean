import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)

abbrev replayInput : Feedback.Input (code inventory pending) :=
  ⟨continuingOpponent inventory pending,
    (laterWords inventory).length + Input.Event.Future.Expiry.horizon epoch.bound⟩

private theorem original_not_empty : epoch.source.seed.original ≠ [] := by
  intro empty
  obtain ⟨item,inside,_⟩ := epoch.source.seed.refused
  rw [empty] at inside
  change item ∈ [] at inside
  cases inside

theorem original_prefix_is_retained : (machine inventory pending).history = [epoch.source.seed.original] := by
  change (if epoch.source.seed.original = [] then [] else [epoch.source.seed.original]) = _
  exact if_neg original_not_empty

private theorem first_response (before : Current) :
    (machine inventory pending).response before = firstWord inventory := by rfl

private theorem first_response_frame :
    (machine inventory pending).responseFrame.word = firstWord inventory := by rfl

private theorem policy_at_original_position (index : Nat) (inside : index < (laterWords inventory).length) :
    (machine inventory pending).feedbackPolicy index =
      some (constant inventory pending (laterWords inventory)[index]) := by
  have actual := Feedback.Execution.policy_at (baseMachine inventory pending) 0 (schedule inventory pending) index
  rw [Nat.zero_add] at actual
  rw [actual]
  simp only [Feedback.Residual.scheduleAt,schedule,List.getElem?_map,List.getElem?_eq_getElem inside,
    Option.map_some,Option.getD_some]

private theorem remaining_at_original_position (count : Nat) :
    ((machine inventory pending).feedbackState (replayInput inventory pending) count).remaining =
      (laterWords inventory).length + Input.Event.Future.Expiry.horizon epoch.bound - count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change ((machine inventory pending).feedbackState (replayInput inventory pending) count).remaining - 1 = _
      rw [ih]
      omega

private theorem word_at_original_position (index : Nat) (inside : index < (laterWords inventory).length) :
    Feedback.word (code inventory pending) ((machine inventory pending).feedbackPolicy index)
      (replayInput inventory pending) ((machine inventory pending).feedbackState (replayInput inventory pending) index) =
      (laterWords inventory)[index] := by
  rw [policy_at_original_position inventory pending index inside]
  have notStopped : ((machine inventory pending).feedbackState (replayInput inventory pending) index).remaining ≠ 0 := by
    rw [remaining_at_original_position]
    omega
  simp only [Feedback.word,Feedback.decision,if_neg notStopped]
  rfl

private def replayPrefix (count : Nat) :=
  [epoch.source.seed.original,firstWord inventory] ++ (laterWords inventory).take count

private theorem replay_prefix_succ (count : Nat) (inside : count < (laterWords inventory).length) :
    replayPrefix inventory (count+1) = replayPrefix inventory count ++ [(laterWords inventory)[count]] := by
  simp only [replayPrefix,List.take_succ_eq_append_getElem inside,List.append_assoc]

theorem feedback_retains_every_actual_word_and_current (count : Nat) (inside : count ≤ (laterWords inventory).length) :
    let actual := (machine inventory pending).feedbackState (replayInput inventory pending) count
    actual.history = replayPrefix inventory count ∧
    actual.current = (replayPrefix inventory count).foldl (Mandate.law base epoch.scope).next
      ((Mandate.law base epoch.scope).next epoch.source.seed.initial []) := by
  induction count with
  | zero =>
      constructor
      · change (machine inventory pending).history ++ [(machine inventory pending).responseFrame.word] = _
        rw [original_prefix_is_retained,first_response_frame]
        rfl
      · change (code inventory pending).law.next
          ((code inventory pending).historyCurrent (machine inventory pending).history)
          (machine inventory pending).responseFrame.word = _
        rw [original_prefix_is_retained,first_response_frame]
        rfl
  | succ count ih =>
      have before := ih (by omega)
      have bounded : count < (laterWords inventory).length := by omega
      have word := word_at_original_position inventory pending count bounded
      have nextPrefix := replay_prefix_succ inventory count bounded
      constructor
      · change ((machine inventory pending).feedbackState (replayInput inventory pending) count).history ++ _ = _
        rw [before.1,word,nextPrefix]
      · change (code inventory pending).law.next
          ((machine inventory pending).feedbackState (replayInput inventory pending) count).current _ = _
        rw [word,before.2,nextPrefix,List.foldl_append,List.foldl_cons,List.foldl_nil]
        rfl

private theorem raw_prefix_fold
    (source : OutstandingSource Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit)
    (inputs : List (List Action)) (seed : OutstandingSource.ExecutionPrefix source) :
    (inputs.foldl OutstandingSource.ExecutionPrefix.append seed).frame.raw =
      inputs.foldl source.seed.law.next seed.frame.raw := by
  induction inputs generalizing seed with
  | nil => rfl
  | cons word tail ih => exact ih (seed.append word)

theorem compiled_cursor_preserves_the_complete_actual_history :
    ((machine inventory pending).feedbackState (replayInput inventory pending) (laterWords inventory).length).history =
      epoch.source.seed.original :: (prepared inventory).inputs := by
  rw [(feedback_retains_every_actual_word_and_current inventory pending _ (Nat.le_refl _)).1]
  simp only [replayPrefix,List.take_length]
  change epoch.source.seed.original :: (firstWord inventory :: laterWords inventory) = _
  rw [received_exact]
  rfl

theorem compiled_cursor_has_the_same_actual_current :
    (machine inventory pending).currentAt (3 + (laterWords inventory).length) =
      current epoch (prepared inventory).inputs := by
  have actual := (machine inventory pending).feedback_current_is_actual (replayInput inventory pending) rfl rfl
    (laterWords inventory).length
  rw [original_prefix_is_retained] at actual
  change (machine inventory pending).currentAt (3 + (laterWords inventory).length) = _ at actual
  rw [actual,(feedback_retains_every_actual_word_and_current inventory pending _ (Nat.le_refl _)).2]
  have source := (OutstandingSource.History.all_finite_inputs_reach_their_own_actual_current
    epoch.source (prepared inventory).inputs).1
  apply Eq.trans ?_ source.symm
  change (replayPrefix inventory (laterWords inventory).length).foldl (Mandate.law base epoch.scope).next
    ((Mandate.law base epoch.scope).next epoch.source.seed.initial []) =
    (((prepared inventory).inputs.foldl OutstandingSource.ExecutionPrefix.append (epoch.source.canonicalPrefix 2)).frame.raw)
  rw [raw_prefix_fold]
  simp only [replayPrefix,List.take_length]
  have received := received_exact inventory
  change firstWord inventory :: laterWords inventory = (prepared inventory).inputs at received
  rw [←received,List.foldl_cons]
  rfl

theorem native_current_is_the_same_actual_cut :
    Native.Authority.currentAt (model inventory pending) (Budget.Programme.Debt.depth (cursor inventory pending)) =
      current epoch (prepared inventory).inputs := by
  change (machine inventory pending).currentAt
    ((machine inventory pending).history.length + 1 + (laterWords inventory).length + 1) = _
  rw [original_prefix_is_retained]
  have address : [epoch.source.seed.original].length + 1 + (laterWords inventory).length + 1 =
      3 + (laterWords inventory).length := by simp only [List.length_singleton];omega
  rw [address]
  exact compiled_cursor_has_the_same_actual_current inventory pending

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource
