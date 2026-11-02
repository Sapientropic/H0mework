import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Replay

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Challenge.Redress.Shared.Iteration.Requests

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction
open Input.Challenge.Redress.Shared.Iteration
noncomputable section

variable {epoch : Epoch}

/-- Commit actual raw submissions at the saved law before asking its joint source
for a response. Responding between words would change the execution's law. -/
def append (inventory : Inventory epoch) : List (List Action) → Inventory epoch
  | [] => inventory
  | word::later => append (World.submit inventory word) later

def appendNative (inventory : Inventory epoch) : (words : List (List Action)) →
    Input.Event.Evolution ⟨epoch,inventory⟩ ⟨epoch,append inventory words⟩
  | [] => .same _
  | word::later => .append (.submit inventory word) (appendNative (World.submit inventory word) later)

theorem inputs_are_the_actual_append (inventory : Inventory epoch) (words : List (List Action)) :
    (append inventory words).inputs = inventory.inputs ++ words := by
  induction words generalizing inventory with
  | nil => exact (List.append_nil _).symm
  | cons word later ih =>
      rw [append,ih]
      change (inventory.inputs ++ [word]) ++ later = _
      simp only [List.append_assoc,List.singleton_append]

theorem current_is_the_raw_fold (inventory : Inventory epoch) (words : List (List Action)) :
    current epoch (append inventory words).inputs =
      words.foldl (Mandate.law base epoch.scope).next (current epoch inventory.inputs) := by
  induction words generalizing inventory with
  | nil => rfl
  | cons word later ih =>
      rw [append,ih]
      rw [show current epoch (World.submit inventory word).inputs =
        (Mandate.law base epoch.scope).next (current epoch inventory.inputs) word from
          Input.Event.observed_current_is_raw_next inventory word]
      rfl

variable (source : Machine Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit)

def words (start count : Nat) : List (List Action) :=
  (List.range count).map fun offset => (source.actualExecution (start+offset)).submitted

theorem source_words_reach_their_actual_current (start count : Nat) :
    (words source start count).foldl source.code.law.next (source.currentAt (start+1)) =
      source.currentAt (start+count+1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [words,List.range_succ,List.map_append,List.map_singleton,List.foldl_append,
        List.foldl_cons,List.foldl_nil]
      rw [show ((List.range count).map fun offset => (source.actualExecution (start+offset)).submitted).foldl
        source.code.law.next (source.currentAt (start+1)) = source.currentAt (start+count+1) from ih]
      simpa only [Nat.add_assoc] using (source.next_is_actual (start+count)).symm

/-- Alignment is an occurrence identity, not a feasibility or success witness.
Every rejection in these raw words is committed by the original law as well. -/
theorem writeback_keeps_the_exact_native_endpoint (inventory : Inventory epoch) (start count : Nat)
    (law : source.code.law = Mandate.law base epoch.scope)
    (aligned : source.currentAt (start+1) = current epoch inventory.inputs) :
    current epoch (append inventory (words source start count)).inputs = source.currentAt (start+count+1) := by
  rw [current_is_the_raw_fold,←law,←aligned]
  exact source_words_reach_their_actual_current source start count


open Input.Challenge.Redress.Shared.Iteration
variable (inventory : Inventory epoch) (start count : Nat) (pending : List Action)

def receive := Requests.produce
  (⟨⟨epoch,append inventory (words source start count)⟩,pending⟩ : Requests.Cursor) []
def next := (receive source inventory start count pending).next

def native : Input.Event.Evolution ⟨epoch,inventory⟩ (next source inventory start count pending).saved :=
  .append (appendNative inventory (words source start count))
    (receive source inventory start count pending).native

def finance := Input.Event.Future.Expiry.Progress.Response.financeAlong (native source inventory start count pending)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Writeback
