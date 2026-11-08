import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumDomain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumEvidence
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open OwnedQuorumSource

theorem every_serialized_body_is_generated_and_verified_in_the_same_actual_history
    (node : Node) (valid : Valid node) (signal : Fin code.signals)
    (body : StageBudget.Ballot (code := code)) (serialized : encoding node signal = some body) :
    body ∈ StageBudget.ledger vocabulary start node.stages ∧
      StageBudget.verify vocabulary start node.stages body = true := by
  have member := List.mem_of_find?_eq_some serialized
  have ledger : ballots node = StageBudget.ledger vocabulary start node.stages := by
    unfold ballots StageBudget.ledger
    rw [valid.2.2]
    rfl
  rw [ledger] at member
  exact ⟨member,decide_eq_true member⟩

theorem a_withheld_owned_opportunity_has_a_real_source_event_and_idle_call
    (node : Node) (requested : Bool) (external : Opponent code) (withheld : withhold node requested = true) :
    ∃ site event, owner node = some site ∧
      localEvent code (base node) site (node.state.frame.inbox site) = some event ∧
      (DemandSchedulePolicy.materialAt node.cursor (protocol node requested) external node.state).call = .own site none ∧
      (DemandSchedulePolicy.materialAt node.cursor (protocol node requested) external node.state).submitted = [] := by
  have selected : opportunity node = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp withheld).1).1
  unfold opportunity at selected
  split at selected <;> try contradiction
  rename_i live
  cases owned : owner node with
  | none => simp only [owned] at selected;cases selected
  | some site =>
    simp only [owned] at selected
    cases intended : localEvent code (base node) site (node.state.frame.inbox site) with
    | none => rw [intended] at selected;cases selected
    | some event =>
      have called : (DemandSchedulePolicy.materialAt node.cursor (protocol node requested) external node.state).call = .own site none := by
        change Distributed.Recall.Information.Agency.ownerAt code node.cursor.ownerStart node.state.history.length = some site at owned
        simp only [DemandSchedulePolicy.materialAt,StageTrace.capture,if_neg live,owned,localEvent,protocol,if_pos withheld]
      refine ⟨site,event,rfl,intended,called,?_⟩
      change word code (some (protocol node requested).work.val)
        ⟨fun _ _ _ => ControlExecution.admitted code
          (DemandSchedulePolicy.materialAt node.cursor (protocol node requested) external node.state).call,node.cursor.entry.budget⟩ node.state = []
      simp only [word,decision,if_neg live,called,ControlExecution.admitted]

def Witness (control : Controller) (external : Nat → Opponent code) (count : Nat) (entry : Nat × Fin code.sites) : Prop :=
  ∃ index < count, let node := actual control external index
    node.cursor.cut = entry.1 ∧ owner node = some entry.2 ∧
      withhold node (control node.cursor.cut node.state) = true

theorem every_actual_omission_is_indexed_by_its_actual_source_prefix
    (control : Controller) (external : Nat → Opponent code) (count : Nat)
    (entry : Nat × Fin code.sites) (member : entry ∈ (actual control external count).omissions) :
    Witness control external count entry := by
  induction count with
  | zero => cases member
  | succ count ih =>
    let node := actual control external count
    let requested := control node.cursor.cut node.state
    change entry ∈ (if withhold node requested then node.omissions ++ [(node.cursor.cut,(owner node).getD 0)] else node.omissions) at member
    by_cases withheld : withhold node requested = true
    · rw [if_pos withheld] at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨index,bounded,rest⟩ := ih earlier
        exact ⟨index,by omega,rest⟩
      · have equal := List.mem_singleton.mp current
        subst entry
        obtain ⟨site,event,owned,_,_,_⟩ := a_withheld_owned_opportunity_has_a_real_source_event_and_idle_call node requested (external node.cursor.cut) withheld
        exact ⟨count,by omega,rfl,by rw [owned];rfl,withheld⟩
    · rw [if_neg withheld] at member
      obtain ⟨index,bounded,rest⟩ := ih member
      exact ⟨index,by omega,rest⟩

theorem actual_rows_preserve_every_earlier_owned_control
    (control : Controller) (external : Nat → Opponent code) (first last : Nat) (later : first ≤ last) :
    (actual control external first).rows <+: (actual control external last).rows := by
  induction last, later using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ last _ ih =>
    exact ih.trans (List.prefix_append _ _)

theorem every_actual_omission_retains_its_actual_idle_occurrence_and_intended_source_event
    (control : Controller) (external : Nat → Opponent code) (count : Nat)
    (entry : Nat × Fin code.sites) (member : entry ∈ (actual control external count).omissions) :
    ∃ index < count, let node := actual control external index
      ∃ row ∈ (actual control external count).rows, ∃ event,
        row.cursor.cut = entry.1 ∧ row.call = .own entry.2 none ∧ row.submitted = [] ∧
        owner node = some entry.2 ∧ localEvent code (base node) entry.2 (node.state.frame.inbox entry.2) = some event := by
  obtain ⟨index,bounded,cut,owned,withheld⟩ := every_actual_omission_is_indexed_by_its_actual_source_prefix control external count entry member
  let node := actual control external index
  let requested := control node.cursor.cut node.state
  let rival := external node.cursor.cut
  obtain ⟨site,event,source,intended,called,submitted⟩ := a_withheld_owned_opportunity_has_a_real_source_event_and_idle_call node requested rival withheld
  have key : site = entry.2 := Option.some.inj (source.symm.trans owned)
  subst site
  let row := DemandSchedulePolicy.materialAt node.cursor (protocol node requested) rival node.state
  have next : row ∈ (actual control external (index + 1)).rows := List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨index,bounded,row,(actual_rows_preserve_every_earlier_owned_control control external (index+1) count (by omega)).subset next,event,cut,called,submitted,owned,intended⟩

theorem local_control_keeps_the_original_source_signing_capability
    (node : Node) (requested : Bool) :
    SourceCapabilityAdmission.check start.source vocabulary (protocol node requested) (RenewedQuorumSource.slot true) = true := by
  change (List.finRange code.sites).all (fun key => decide
    (ProtocolCapabilityBudget.choices start.source (DemandSchedulePolicy.work true) vocabulary (RenewedQuorumSource.slot true) key ⊆
    SourceCapabilityAdmission.choices start.source vocabulary (RenewedQuorumSource.slot true) key)) = true
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumEvidence
