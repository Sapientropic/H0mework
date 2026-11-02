import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Projection
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Distributed.Reaction.Native.Future.Recovery

structure State where
  inputs : List (List Action)
  consumed : List Action
  residual : List Action

variable (epoch : Epoch)
def context (inputs : List (List Action)) : Search.Context
    (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit) :=
  ⟨base,epoch.scope,epoch.source.seed.actionsAt (current epoch inputs),[.feedstock,.service],epoch.source.seed.budget⟩

def pending (inputs : List (List Action)) (word : List Action) :=
  ((Mandate.law base epoch.scope).rawItems (current epoch inputs) word).filterMap fun item =>
    if ¬ (Mandate.law base epoch.scope).Valid item.before item.request then some item.request else none

def begin (inputs : List (List Action)) (word : List Action) : State :=
  ⟨inputs ++ [word],[],pending epoch inputs word⟩

def proposal (state : State) (actor : Bool) :=
  Search.selected (context epoch state.inputs) (current epoch state.inputs) actor state.residual

def quality (state : State) (actor : Bool) :=
  (proposal epoch state actor).quality (context epoch state.inputs) (current epoch state.inputs) state.residual

def advance (state : State) (actor : Bool) : State :=
  let model := context epoch state.inputs
  let before := current epoch state.inputs
  let chosen := proposal epoch state actor
  let retry := chosen.retry model before state.residual
  ⟨state.inputs ++ [chosen.word model before state.residual],state.consumed ++ retry.consumed,retry.residual⟩

/-- The finite evaluator observes the existing search and actual emitted words.
It carries no authority, completion or native-account witness. -/
def run : Nat → State → State
  | 0,state => state
  | fuel+1,state => match state.residual with
    | [] => state
    | head::_ =>
      if 0 < quality epoch state head.signer then run fuel (advance epoch state head.signer)
      else advance epoch state head.signer

def produce (inputs : List (List Action)) (word : List Action) :=
  let first := begin epoch inputs word
  run epoch (first.residual.length+1) first

noncomputable section
variable {epoch} {inventory : Inventory epoch} {word : List Action}

def read (cursor : Recovery.Cursor inventory word) : State :=
  ⟨cursor.saved.inputs,cursor.consumed,cursor.residual⟩

theorem context_is_the_actual_source (cursor : Recovery.Cursor inventory word) :
    context epoch (read cursor).inputs = cursor.model := rfl

theorem advance_is_the_actual_full_inventory_submission (cursor : Recovery.Cursor inventory word) (actor : Bool) :
    advance epoch (read cursor) actor = read (cursor.advance actor) := rfl

private theorem filter_original_refusals (items : List (ExecutionItem Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit)) :
    (items.attach.filterMap (fun item =>
      if ¬ (Mandate.law base epoch.scope).Valid item.val.before item.val.request
      then some item.val.request else none)) =
    items.filterMap (fun item =>
      if ¬ (Mandate.law base epoch.scope).Valid item.before item.request
      then some item.request else none) := by
  let select := fun (item : ExecutionItem Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit) =>
    if ¬ (Mandate.law base epoch.scope).Valid item.before item.request then some item.request else none
  calc
    _ = List.filterMap select (items.attach.map Subtype.val) :=
      (List.filterMap_map (l := items.attach) (f := Subtype.val) (g := select)).symm
    _ = _ := by rw [List.attach_map_subtype_val]

theorem begin_is_the_actual_refused_input (inventory : Inventory epoch) (word : List Action) :
    begin epoch inventory.inputs word = read (Recovery.begin inventory word) := by
  apply congrArg (fun remaining => State.mk (inventory.inputs ++ [word]) [] remaining)
  change _ = (Recovery.origins inventory word).map (fun entry => entry.item.request)
  unfold pending Recovery.origins
  rw [List.map_filterMap,←filter_original_refusals]
  apply congrArg (fun select => List.filterMap select
    ((Mandate.law base epoch.scope).rawItems (current epoch inventory.inputs) word).attach)
  funext item
  split_ifs <;> rfl

theorem follows_the_original_trace (cursor : Recovery.Cursor inventory word)
    (trace : Recovery.Trace inventory word cursor) (fuel : Nat) (enough : cursor.residual.length < fuel) :
    run epoch fuel (read cursor) = read trace.finish := by
  induction trace generalizing fuel with
  | finished cursor empty =>
      cases fuel <;> simp only [run,read,empty,Recovery.Trace.finish]
  | blocked cursor head tail remaining stopped =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          change (match cursor.residual with
            | [] => read cursor
            | first::_ => if 0 < quality epoch (read cursor) first.signer
              then run epoch fuel (advance epoch (read cursor) first.signer)
              else advance epoch (read cursor) first.signer) = _
          rw [remaining]
          change (if 0 < cursor.quality head.signer then _ else _) = _
          rw [if_neg stopped]
          exact advance_is_the_actual_full_inventory_submission cursor head.signer
  | advanced cursor head tail remaining progress later ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          change (match cursor.residual with
            | [] => read cursor
            | first::_ => if 0 < quality epoch (read cursor) first.signer
              then run epoch fuel (advance epoch (read cursor) first.signer)
              else advance epoch (read cursor) first.signer) = _
          rw [remaining]
          change (if 0 < cursor.quality head.signer then _ else _) = _
          rw [if_pos progress,advance_is_the_actual_full_inventory_submission]
          exact ih fuel (by have decrease := cursor.positive_progress head.signer progress;omega)

theorem the_computable_observation_is_the_same_original_root_trace (inventory : Inventory epoch) (word : List Action) :
    produce epoch inventory.inputs word = read (Runtime.read inventory word).finish := by
  unfold produce
  rw [begin_is_the_actual_refused_input]
  exact follows_the_original_trace (Recovery.begin inventory word) (Recovery.produce inventory word) _ (Nat.lt_succ_self _)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Projection
