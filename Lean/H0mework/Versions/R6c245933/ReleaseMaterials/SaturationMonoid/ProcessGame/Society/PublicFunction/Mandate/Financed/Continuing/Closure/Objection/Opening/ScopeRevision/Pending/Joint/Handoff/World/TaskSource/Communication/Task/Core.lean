import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Source

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Admission

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section

variable {epoch : Epoch} (inventory : Inventory epoch) (pending : List Action)
  (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)) (old : Cursor prior.model.source.code)

def rule (original : Rule prior.model.source.code) : Rule (Source.code inventory old) := by
  refine ⟨original.work,?_⟩
  intro key inside
  refine ⟨(original.events key inside).val,?_⟩
  have member := (original.events key inside).property
  simp only [ownMoves,List.mem_cons,List.mem_map,List.mem_filter] at member ⊢
  rcases member with absent | ⟨event,⟨supported,owned⟩,same⟩
  · exact Or.inl absent
  · refine Or.inr ⟨event,⟨supported,?_⟩,same⟩
    rcases event with ⟨event,supported⟩
    cases event <;> simp only [decide_eq_true_eq,Bool.false_eq_true] at owned ⊢ <;> exact owned

/-- A view for the old response function only; this never installs an old
frame or legality flag into the new emitter. -/
def readFrame (actual : (Source.code inventory old).Frame) : prior.model.source.code.Frame :=
  ⟨actual.word,actual.sent.map (fun packet => ⟨packet.sender,packet.recipient,packet.signal,packet.sentAfter⟩),
    actual.inbox,actual.localLegal⟩

def rival : Opponent (Source.code inventory old) := fun history past frame =>
  prior.rival history past (readFrame inventory prior old frame)

/-- Every original position is reconstructed by its own actual emitter.
The first position is the actual post-Service cut, which need not belong to
the original planning domain. Repeated positions retain their allocation. -/
def reconstructDomain {original : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit}
    (points : List (Cursor original)) (actual : Cursor original) :
    List (Cursor (Source.code inventory actual)) :=
  (actual :: points).map fun point => Source.cursor inventory point

def domain : List (Cursor (Source.code inventory old)) :=
  reconstructDomain inventory prior.domain old

theorem every_original_position_is_reconstructed
    (point : Cursor prior.model.source.code) (member : point ∈ prior.domain) :
    Source.cursor inventory point ∈ domain inventory prior old :=
  List.mem_map.mpr ⟨point,List.mem_cons_of_mem _ member,rfl⟩

theorem original_positions_keep_their_order (index : Nat) :
    (domain inventory prior old)[index+1]? =
      (prior.domain[index]?).map (fun point => Source.cursor inventory point) := by
  simp only [domain,reconstructDomain,List.getElem?_map,List.getElem?_cons_succ]

private theorem remaining_does_not_shrink (point : Cursor prior.model.source.code) :
    Feedback.Cut.horizon point.source point.entry point.cut ≤
      Feedback.Cut.horizon (Source.cursor inventory point).source
        (Source.cursor inventory point).entry (Source.cursor inventory point).cut := by
  rw [show Feedback.Cut.horizon (Source.cursor inventory point).source
      (Source.cursor inventory point).entry (Source.cursor inventory point).cut =
      ((Source.machine inventory point).feedbackState (Source.input inventory point)
        (Source.commands inventory point).length).remaining by rfl,
    Source.replay_keeps_the_old_budget_and_the_new_source_horizon]
  exact Nat.le_max_left _ _

theorem complete_original_horizon_is_retained :
    horizon prior.domain ≤ horizon (domain inventory prior old) := by
  have each (points : List (Cursor prior.model.source.code)) :
      horizon points ≤ horizon (code := Source.code inventory old)
        (points.map (fun point => (Source.cursor inventory point : Cursor (Source.code inventory old)))) := by
    induction points with
    | nil => exact Nat.le_refl 0
    | cons point later ih =>
        exact max_le_max (remaining_does_not_shrink inventory prior point) ih
  exact (each prior.domain).trans (Nat.le_max_right _ _)

/-- Original Task, planner and full relation; its actual view and World input
come from the same new-law emitter and its complete native writeback. -/
def task : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) where
  model := Source.model inventory old
  domain := domain inventory prior old
  original := rule inventory prior old prior.original
  baseline := ⟨(prior.baseline.controls.map (rule inventory prior old)).take
    (horizon (domain inventory prior old)),by
      exact (List.length_take_le _ _)⟩
  point := Owned.PublicTask.currentView (Source.cursor inventory old)
  rival := rival inventory prior old
  reader := prior.reader
  quote := prior.quote
  recoveryRate := prior.recoveryRate
  accountingRate := prior.accountingRate
  futureRequests := prior.futureRequests ++ TaskSource.ports.map
    (fun intent => pending ++ Input.emit (Source.saved inventory old) intent)
  worldInput := some (.actual (Source.saved inventory old))
  worldPending := pending
  worldCurrent := some ⟨by
    intro input supplied
    cases (Option.some.inj supplied).symm
    refine ⟨rfl,?_⟩
    change (Source.cursor inventory old).source.currentAt
      ((Source.cursor inventory old).source.history.length+1+(Source.cursor inventory old).cut+1) = _
    rw [show (Source.cursor inventory old).source.history.length = 0 by rfl]
    rw [show 0+1+(Source.cursor inventory old).cut+1 = 2+(Source.cursor inventory old).cut by omega]
    exact Source.cursor_current_is_the_same_written_world inventory old⟩
  vocabulary := prior.vocabulary
  encoding := prior.encoding
  law := ⟨prior.law.scope,prior.law.maxDelay⟩
  continueUnreserved := prior.continueUnreserved

theorem complete_original_baseline_is_retained :
    (task inventory pending prior old).baseline.controls =
      prior.baseline.controls.map (rule inventory prior old) := by
  change (prior.baseline.controls.map (rule inventory prior old)).take
    (horizon (domain inventory prior old)) = _
  apply List.take_of_length_le
  simpa only [List.length_map] using
    prior.baseline.bounded.trans (complete_original_horizon_is_retained inventory prior old)

theorem original_task_receives_the_actual_reconstructed_cursor :
    (task inventory pending prior old).point.point = Source.cursor inventory old ∧
    (task inventory pending prior old).worldInput = some (.actual (Source.saved inventory old)) := ⟨rfl,rfl⟩

theorem original_task_cut_is_the_same_actual_world :
    Native.Authority.currentAt (task inventory pending prior old).model
      (Budget.Programme.Debt.depth (task inventory pending prior old).point.point) =
      current epoch (Source.saved inventory old).inputs := by
  change (Source.cursor inventory old).source.currentAt
    ((Source.cursor inventory old).source.history.length+1+(Source.cursor inventory old).cut+1) = _
  rw [show (Source.cursor inventory old).source.history.length = 0 by rfl]
  rw [show 0+1+(Source.cursor inventory old).cut+1 = 2+(Source.cursor inventory old).cut by omega]
  exact Source.cursor_current_is_the_same_written_world inventory old

def admit := Owned.Source.seed (task inventory pending prior old)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication
