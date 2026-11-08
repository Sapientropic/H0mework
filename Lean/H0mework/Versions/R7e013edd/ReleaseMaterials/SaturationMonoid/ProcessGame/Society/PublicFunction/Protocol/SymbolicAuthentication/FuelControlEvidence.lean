import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlDomain

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlEvidence
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open FuelControlSource

theorem a_withheld_owned_opportunity_has_a_real_source_event_and_idle_call
    (node : Node) (requested : Bool) (external : Opponent code) (withheld : withhold node requested = true) :
    ∃ site event, owner node = some site ∧
      localEvent code base site (node.state.frame.inbox site) = some event ∧
      (material node requested external).call = .own site none ∧
      (material node requested external).submitted = [] := by
  have selected : opportunity node = true := (Bool.and_eq_true_iff.mp withheld).1
  unfold opportunity at selected
  split at selected <;> try contradiction
  rename_i live
  cases owned : owner node with
  | none => simp only [owned] at selected;cases selected
  | some site =>
    simp only [owned] at selected
    cases intended : localEvent code base site (node.state.frame.inbox site) with
    | none => rw [intended] at selected;cases selected
    | some event =>
      have called : (material node requested external).call = .own site none := by
        change Distributed.Recall.Information.Agency.ownerAt code node.cursor.ownerStart node.state.history.length = some site at owned
        simp only [material,StageTrace.capture,if_neg live,owned,localEvent,protocol,if_pos withheld]
      refine ⟨site,event,rfl,intended,called,?_⟩
      change word code (some (protocol node requested).work.val)
        ⟨fun _ _ _ => ControlExecution.admitted code
          (material node requested external).call,node.cursor.entry.budget⟩ node.state = []
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
        owner node = some entry.2 ∧ localEvent code base entry.2 (node.state.frame.inbox entry.2) = some event := by
  obtain ⟨index,bounded,cut,owned,withheld⟩ := every_actual_omission_is_indexed_by_its_actual_source_prefix control external count entry member
  let node := actual control external index
  let requested := control node.cursor.cut node.state
  let rival := external node.cursor.cut
  obtain ⟨site,event,source,intended,called,submitted⟩ := a_withheld_owned_opportunity_has_a_real_source_event_and_idle_call node requested rival withheld
  have key : site = entry.2 := Option.some.inj (source.symm.trans owned)
  subst site
  let row := material node requested rival
  have next : row ∈ (actual control external (index + 1)).rows := List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨index,bounded,row,(actual_rows_preserve_every_earlier_owned_control control external (index+1) count (by omega)).subset next,event,cut,called,submitted,owned,intended⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FuelControlEvidence
