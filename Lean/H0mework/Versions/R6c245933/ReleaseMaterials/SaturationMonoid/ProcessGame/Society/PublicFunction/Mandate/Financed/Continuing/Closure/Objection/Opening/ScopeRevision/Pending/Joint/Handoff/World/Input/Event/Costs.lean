import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Visits

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Costs

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup

noncomputable section
abbrev Visits := PublicFunction.Costs.Visits.Window sources

/-- Match the very source/visit consumed by financeAlong, including bootstrap
and the original refused request when a new source is entered. -/
def records {first last : Packet} : Evolution first last → List Visits
  | .same _ => []
  | @Evolution.submit epoch inventory word => PublicFunction.Costs.Visits.interval sources
      (World.I epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2) 1
  | .handoff _ fresh => PublicFunction.Costs.Visits.interval sources (Handoff.I fresh) 0 4
  | .handoffAt _ fresh actualInputs => PublicFunction.Costs.Visits.interval sources
      (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2)
  | .append earlier later => records earlier ++ records later

def cost {first last : Packet} (path : Evolution first last) (bearer : Bool) :=
  PublicFunction.Costs.Visits.total sources (records path) bearer

def credits {first last : Packet} (path : Evolution first last) (bearer : Bool) (good : Good) :=
  PublicFunction.Costs.Visits.credits sources (records path) bearer good

private theorem opening_before {epoch : Epoch} (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    PublicFunction.Costs.Visits.rawAt sources (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 =
      current epoch inventory.inputs := by rfl

private theorem opening_after {epoch : Epoch} (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (actualInputs : List (List Action)) :
    PublicFunction.Costs.Visits.rawAt sources (OutstandingSource.History.input (Handoff.source fresh) actualInputs)
      (actualInputs.length+2) = current (Epoch.ofFresh fresh) (World.handoffAt inventory fresh actualInputs).inputs := by rfl

theorem material_balance {first last : Packet} (path : Evolution first last) (bearer : Bool) (good : Good) :
    (current last.1 last.2.inputs).stock bearer good +
      cost path bearer (.operating good) + cost path bearer (.debtPayment good) =
    (current first.1 first.2.inputs).stock bearer good + credits path bearer good := by
  induction path with
  | same packet => simp only [cost, credits, records, PublicFunction.Costs.Visits.total,
      PublicFunction.Costs.Visits.credits, Pi.zero_apply, add_zero]
  | @submit epoch inventory word =>
      have first : PublicFunction.Costs.Visits.rawAt sources (World.I epoch (inventory.inputs ++ [word]))
          (inventory.inputs.length + 2) = current epoch inventory.inputs :=
        Mandate.Challenge.Cross.emitted_word_uses_actual_cut epoch.bound inventory.inputs word
      have last : PublicFunction.Costs.Visits.rawAt sources (World.I epoch (inventory.inputs ++ [word]))
          (inventory.inputs.length + 2 + 1) = current epoch (World.submit inventory word).inputs := by
        change OutstandingSource.History.currentAt epoch.source (inventory.inputs ++ [word])
          (inventory.inputs.length + 2 + 1) =
          OutstandingSource.History.currentAt epoch.source (inventory.inputs ++ [word])
            ((inventory.inputs ++ [word]).length + 2)
        simp only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.reduceAdd]
      have balance := PublicFunction.Costs.Visits.interval_material sources
        (World.I epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2) 1 bearer good
      rw [first, last] at balance
      exact balance
  | handoff inventory fresh =>
      exact PublicFunction.Costs.Visits.interval_material sources (Handoff.I fresh) 0 4 bearer good
  | handoffAt inventory fresh actualInputs =>
      have balance := PublicFunction.Costs.Visits.interval_material sources
        (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2) bearer good
      rw [Nat.zero_add,opening_after inventory fresh actualInputs,opening_before inventory fresh actualInputs] at balance
      exact balance
  | append earlier later ih₁ ih₂ =>
      change _ + PublicFunction.Costs.Visits.total sources (records earlier ++ records later) bearer (.operating good) +
        PublicFunction.Costs.Visits.total sources (records earlier ++ records later) bearer (.debtPayment good) =
        _ + PublicFunction.Costs.Visits.credits sources (records earlier ++ records later) bearer good
      rw [PublicFunction.Costs.Visits.total_append, PublicFunction.Costs.Visits.credits_append]
      change _ + (cost earlier bearer (.operating good) + cost later bearer (.operating good)) +
        (cost earlier bearer (.debtPayment good) + cost later bearer (.debtPayment good)) =
        _ + (credits earlier bearer good + credits later bearer good)
      linarith

theorem elapsed_exact {first last : Packet} (path : Evolution first last) (bearer : Bool) :
    cost path bearer .elapsed = (current last.1 last.2.inputs).clock - (current first.1 first.2.inputs).clock := by
  induction path with
  | same packet => simp only [cost, records, PublicFunction.Costs.Visits.total, Pi.zero_apply, sub_self]
  | @submit epoch inventory word =>
      have timing := PublicFunction.Costs.Visits.interval_elapsed sources
        (World.I epoch (inventory.inputs ++ [word])) (inventory.inputs.length + 2) 1 bearer
      have before : PublicFunction.Costs.Visits.rawAt sources (World.I epoch (inventory.inputs ++ [word]))
          (inventory.inputs.length + 2) = current epoch inventory.inputs :=
        Mandate.Challenge.Cross.emitted_word_uses_actual_cut epoch.bound inventory.inputs word
      have after : PublicFunction.Costs.Visits.rawAt sources (World.I epoch (inventory.inputs ++ [word]))
          (inventory.inputs.length + 2 + 1) = current epoch (World.submit inventory word).inputs := by
        change OutstandingSource.History.currentAt epoch.source (inventory.inputs ++ [word])
          (inventory.inputs.length + 2 + 1) =
          OutstandingSource.History.currentAt epoch.source (inventory.inputs ++ [word])
            ((inventory.inputs ++ [word]).length + 2)
        simp only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.reduceAdd]
      rw [before, after] at timing
      exact timing
  | handoff inventory fresh =>
      exact PublicFunction.Costs.Visits.interval_elapsed sources (Handoff.I fresh) 0 4 bearer
  | handoffAt inventory fresh actualInputs =>
      have timing := PublicFunction.Costs.Visits.interval_elapsed sources
        (OutstandingSource.History.input (Handoff.source fresh) actualInputs) 0 (actualInputs.length+2) bearer
      rw [Nat.zero_add,opening_after inventory fresh actualInputs,opening_before inventory fresh actualInputs] at timing
      exact timing
  | append earlier later ih₁ ih₂ =>
      change PublicFunction.Costs.Visits.total sources (records earlier ++ records later) bearer .elapsed = _
      rw [PublicFunction.Costs.Visits.total_append]
      change cost earlier bearer .elapsed + cost later bearer .elapsed = _
      rw [ih₁, ih₂]
      ring

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Costs
