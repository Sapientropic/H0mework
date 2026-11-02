import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)
  {originInputs : List (List Action)} {start : Inventory ready originInputs}

structure Descendant (original : Mandate.Challenge.Cross.Resident (B ready) start.inputs) (inventory : Inventory ready originInputs) where
  private mk ::
  thread : Mandate.Challenge.Cross.History (Mandate.Challenge.fromHistory (B ready)) original.original inventory.inputs
  within : Mandate.Challenge.Cross.History.Within (B ready) (inventory.inputs.length + 2) thread
  present : (⟨original.originInputs, original.original, thread, within⟩ : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) ∈ inventory.objections
  crossing : (Mandate.Challenge.Cross.process (Mandate.Challenge.fromHistory (B ready)) original.original).Run original.history.state.current thread.state.current

noncomputable def begin (inventory : Inventory ready originInputs)
    (original : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) (inside : original ∈ inventory.objections) :
    Descendant ready original inventory := ⟨original.history, original.within, inside, .nil⟩

noncomputable def Descendant.step {original : Mandate.Challenge.Cross.Resident (B ready) start.inputs} {inventory : Inventory ready originInputs}
    (descendant : Descendant ready original inventory) (word : List Action) : Descendant ready original (submit ready inventory word) :=
  let resident : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs :=
    ⟨original.originInputs, original.original, descendant.thread, descendant.within⟩
  let next := resident.advance (B ready) word
  ⟨next.history, next.within, every_old_objection_is_in_the_next_inventory ready inventory word resident descendant.present,
    descendant.crossing.concatRuns _ (resident.responseRun (B ready) word)⟩

noncomputable def Descendant.responses {original : Mandate.Challenge.Cross.Resident (B ready) start.inputs} {inventory : Inventory ready originInputs}
    (descendant : Descendant ready original inventory) : (count : Nat) → Descendant ready original (run ready inventory count)
  | 0 => descendant
  | count + 1 => Descendant.step ready (descendant.responses count) (emit ready (run ready inventory count))

noncomputable def Descendant.alternating {original : Mandate.Challenge.Cross.Resident (B ready) start.inputs} {inventory : Inventory ready originInputs}
    (descendant : Descendant ready original inventory) : (words : List (List Action)) → Descendant ready original (alternate ready inventory words)
  | [] => descendant
  | word :: tail => (Descendant.step ready (Descendant.step ready descendant (emit ready inventory)) word).alternating tail

noncomputable def every_original_survives_finite_responses (inventory : Inventory ready originInputs)
    (original : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) (inside : original ∈ inventory.objections) (count : Nat) :
    Descendant ready original (run ready inventory count) := Descendant.responses ready (begin ready inventory original inside) count

noncomputable def every_original_survives_finite_alternation (inventory : Inventory ready originInputs)
    (original : Mandate.Challenge.Cross.Resident (B ready) inventory.inputs) (inside : original ∈ inventory.objections) (words : List (List Action)) :
    Descendant ready original (alternate ready inventory words) := Descendant.alternating ready (begin ready inventory original inside) words

noncomputable def every_newborn_survives_finite_alternation (inventory : Inventory ready originInputs) (word : List Action)
    (resident : Mandate.Challenge.Cross.Resident (B ready) (submit ready inventory word).inputs)
    (born : resident ∈ Mandate.Challenge.Cross.newborn (B ready) (inputs := inventory.inputs) word) (words : List (List Action)) :
    Descendant ready resident (alternate ready (submit ready inventory word) words) :=
  Descendant.alternating ready (begin ready (submit ready inventory word) resident (List.mem_append_right _ born)) words

noncomputable def services_finitely_continue (inventory : Inventory ready originInputs) (index : (epochSource ready).Slot) : (count : Nat) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((run ready inventory count).services index).state.current
  | 0 => .nil
  | count + 1 => (services_finitely_continue inventory index count).concatRuns _
      (every_original_service_has_actual_native_continuation ready (run ready inventory count) (emit ready (run ready inventory count)) index)

noncomputable def services_alternately_continue (inventory : Inventory ready originInputs) (index : (epochSource ready).Slot) : (words : List (List Action)) →
    (OutstandingSource.History.NativeService.threadProcess (epochSource ready) originInputs).Run
      (inventory.services index).state.current ((alternate ready inventory words).services index).state.current
  | [] => .nil
  | word :: tail =>
    ((every_original_service_has_actual_native_continuation ready inventory (emit ready inventory) index).concatRuns _
      (every_original_service_has_actual_native_continuation ready (advance ready inventory) word index)).concatRuns _
        (services_alternately_continue (submit ready (advance ready inventory) word) index tail)

noncomputable def finance_finitely_continues (inventory : Inventory ready originInputs) : (count : Nat) →
    (Institutions.Capitalism.Universal.Root.Financial.Family.process Finance.sources).Run
      inventory.finance.current (run ready inventory count).finance.current
  | 0 => .nil
  | count + 1 => (finance_finitely_continues inventory count).concatRuns _
      (every_original_financial_slot_has_actual_native_continuation ready (run ready inventory count)
        (emit ready (run ready inventory count)))

noncomputable def finance_alternately_continues (inventory : Inventory ready originInputs) : (words : List (List Action)) →
    (Institutions.Capitalism.Universal.Root.Financial.Family.process Finance.sources).Run
      inventory.finance.current (alternate ready inventory words).finance.current
  | [] => .nil
  | word :: tail =>
    ((every_original_financial_slot_has_actual_native_continuation ready inventory (emit ready inventory)).concatRuns _
      (every_original_financial_slot_has_actual_native_continuation ready (advance ready inventory) word)).concatRuns _
        (finance_alternately_continues (submit ready (advance ready inventory) word) tail)

noncomputable def each_financial_debt_alternately_continues (inventory : Inventory ready originInputs) (words : List (List Action))
    (index : Nat) (slot : ObligationSlot (Institutions.Capitalism.Universal.Root.Financial.Family.vocabulary Finance.sources))
    (present : inventory.finance.current.slots[index]? = some slot) :=
  Institutions.Capitalism.Universal.Root.Financial.Family.Migration.follow Finance.sources
    (finance_alternately_continues ready inventory words) index slot present

theorem service_history_is_the_entire_generated_run (inventory : Inventory ready originInputs) (index : (epochSource ready).Slot) :
    (inventory.services index).state.current.history = (inventory.services index).state.generated.events :=
  (inventory.services index).actual_history (epochSource ready)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
