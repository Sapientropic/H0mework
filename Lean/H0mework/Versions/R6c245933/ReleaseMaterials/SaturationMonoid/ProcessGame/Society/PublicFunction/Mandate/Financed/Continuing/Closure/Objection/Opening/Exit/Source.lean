import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Supply
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Progress
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Release

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ} {inputs : List (List Action)}

def emit (inventory : Joint.Inventory fuel) : List Action :=
  match inventory.cut.past.frame.raw.technology.holder with
  | some actor => word inventory.cut.past.frame.raw actor
  | none => Opening.emit inventory

theorem holder_emission (inventory : Joint.Inventory fuel) (actor : Bool)
    (holder : inventory.cut.past.frame.raw.technology.holder = some actor) :
    emit inventory = signedWord (suffix inventory.cut.past.frame.raw actor) := by
  simp only [emit, holder, word_is_signed]

theorem holder_is_active (current : Current) (actor : Bool) (holder : current.technology.holder = some actor) :
    Mandate.Response.Active current := Or.inl (by rw [holder]; rfl)

theorem supplies_for_the_blocked_holder (current : Current) (actor : Bool)
    (holder : current.technology.holder = some actor) (blocked : choose current actor = none) :
    ∃ event ∈ supplies current actor, 0 < event.demand.quantity ∧ event.item ∈ law.rawItems current (word current actor) := by
  obtain ⟨demand, present⟩ := blocked_holder_has_a_positive_repair current actor holder blocked
  have original : demand ∈ (supplies current actor).map SupplyEvent.demand := by
    rwa [supplies, supply_trace_keeps_every_original_demand]
  obtain ⟨event, included, same⟩ := List.mem_map.mp original
  exact ⟨event, included, by rw [same]; exact demand.shortfall, every_supply_is_in_the_original_word current actor event included⟩

inductive Outcome (current : Current) (actor : Bool) where
  | private paid (ready : Ready current actor) (selected : choose current actor = some ready)
      (retired : (law.execute current 0 (word current actor)).final.technology.holder = none ∧
        (law.execute current 0 (word current actor)).final.technology.offered = none)
  | private repair (blocked : choose current actor = none)
      (attempted : ∃ event ∈ supplies current actor, 0 < event.demand.quantity ∧
        event.item ∈ law.rawItems current (word current actor))

def outcome (current : Current) (actor : Bool) (holder : current.technology.holder = some actor) : Outcome current actor :=
  match selected : choose current actor with
  | some ready => .paid ready selected (paid_word_retires_its_actual_holder current actor ready selected)
  | none => .repair selected (supplies_for_the_blocked_holder current actor holder selected)

structure HolderReceipt (inventory : Joint.Inventory fuel) (actor : Bool) where
  private mk ::
  holder : inventory.cut.past.frame.raw.technology.holder = some actor
  emitted : emit inventory = signedWord (suffix inventory.cut.past.frame.raw actor)
  claim : Claim fuel (branchInputs inventory.cut (signedWord (suffix inventory.cut.past.frame.raw actor)))
  decoded : read fuel _ (signaturePosition inventory.cut (suffix inventory.cut.past.frame.raw actor)) = some claim
  snapshot : claim.snapshot = inventory.cut.past.frame.raw.technology
  response : Outcome inventory.cut.past.frame.raw actor
  supply : List (SupplyEvent inventory.cut.past.frame.raw actor)
  supply_exact : supply = supplies inventory.cut.past.frame.raw actor

inductive Receipt (inventory : Joint.Inventory fuel) where
  | private held (actor : Bool) (receipt : HolderReceipt inventory actor)
  | private noHolder (absent : inventory.cut.past.frame.raw.technology.holder = none)
      (emitted : emit inventory = Opening.emit inventory)
      (opening : Opening.Receipt inventory) (opening_exact : opening = Opening.generate inventory)

def generate (inventory : Joint.Inventory fuel) : Receipt inventory :=
  match holder : inventory.cut.past.frame.raw.technology.holder with
  | some actor =>
    let active := holder_is_active _ actor holder
    .held actor ⟨holder, holder_emission inventory actor holder,
      signature inventory.cut (suffix inventory.cut.past.frame.raw actor) active,
      signature_is_actually_read inventory.cut (suffix inventory.cut.past.frame.raw actor) active,
      signature_snapshot_is_the_actual_cut inventory.cut (suffix inventory.cut.past.frame.raw actor) active,
      outcome inventory.cut.past.frame.raw actor holder, supplies inventory.cut.past.frame.raw actor, rfl⟩
  | none => .noHolder holder (by simp only [emit, holder]) (Opening.generate inventory) rfl

def advance (inventory : Joint.Inventory fuel) := Joint.submit inventory (emit inventory)

def run (inventory : Joint.Inventory fuel) : Nat → Joint.Inventory fuel
  | 0 => inventory
  | count + 1 => advance (run inventory count)

def alternate (inventory : Joint.Inventory fuel) : List (List Action) → Joint.Inventory fuel
  | [] => inventory
  | word :: tail => alternate (Joint.submit (advance inventory) word) tail

def alternatingDescendants {start : Joint.Inventory fuel} {original : Joint.Row start.cut} {inventory : Joint.Inventory fuel}
    (descendant : Joint.Descendant original inventory) : (words : List (List Action)) → Joint.Descendant original (alternate inventory words)
  | [] => descendant
  | word :: tail => alternatingDescendants ((descendant.step (emit inventory)).step word) tail

def every_old_responsibility_survives (inventory : Joint.Inventory fuel) (row : Joint.Row inventory.cut)
    (inside : row ∈ inventory.frame.rows) (words : List (List Action)) : Joint.Descendant row (alternate inventory words) :=
  alternatingDescendants (Joint.begin inventory row inside) words

theorem every_pending_row_keeps_the_holders_actual_challenge (inventory : Joint.Inventory fuel)
    (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows)
    (actor : Bool) (holder : inventory.cut.past.frame.raw.technology.holder = some actor) (pending : row.isPending = true) :
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (Joint.carry inventory (emit inventory) row inside).thread.history.state.current.history.map LifecycleEvent.kind := by
  rw [(Joint.carry inventory (emit inventory) row inside).exact_thread, holder_emission inventory actor holder]
  exact every_pending_thread_gains_progress_in_the_actual_word inventory.cut (suffix inventory.cut.past.frame.raw actor)
    (holder_is_active _ actor holder) row.2 pending

theorem every_active_pending_row_keeps_actual_progress (inventory : Joint.Inventory fuel)
    (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) (pending : row.isPending = true) :
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (Joint.carry inventory (emit inventory) row inside).thread.history.state.current.history.map LifecycleEvent.kind := by
  cases holder : inventory.cut.past.frame.raw.technology.holder with
  | some actor => exact every_pending_row_keeps_the_holders_actual_challenge inventory row inside actor holder pending
  | none =>
    have emitted : emit inventory = Opening.emit inventory := by simp only [emit, holder]
    rw [emitted]
    exact every_carried_pending_row_keeps_its_source_progress inventory row inside active pending

abbrev inputItems (inventory : Joint.Inventory fuel) :=
  Lifecycle.Observed.Release.items (base := base) (scope := scope)
    (currentAt := Runtime.mandateCurrentAt fuel (branchInputs inventory.cut (emit inventory)))
    (wordAt := Runtime.mandateWordAt fuel (branchInputs inventory.cut (emit inventory))) (inventory.cut.depth + 1)

abbrev beforeInput (inventory : Joint.Inventory fuel) (birth : Fin (inventory.cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel (branchInputs inventory.cut (emit inventory)) birth.val)
      (Runtime.mandateWordAt fuel (branchInputs inventory.cut (emit inventory)) birth.val)) :=
  (Runtime.traceGrant fuel (branchInputs inventory.cut (emit inventory)) birth.val inventory.cut.depth grant).continuation

abbrev ReleaseAt (inventory : Joint.Inventory fuel) (birth : Fin (inventory.cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel (branchInputs inventory.cut (emit inventory)) birth.val)
      (Runtime.mandateWordAt fuel (branchInputs inventory.cut (emit inventory)) birth.val))
    (index : Fin (inputItems inventory).length) :=
  Lifecycle.Observed.Release.Receipt (beforeInput inventory birth grant) (inventory.cut.depth + 1) index

def readRelease (inventory : Joint.Inventory fuel) (birth : Fin (inventory.cut.depth + 1))
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel (branchInputs inventory.cut (emit inventory)) birth.val)
      (Runtime.mandateWordAt fuel (branchInputs inventory.cut (emit inventory)) birth.val))
    (index : Fin (inputItems inventory).length) :=
  Lifecycle.Observed.Release.read (beforeInput inventory birth grant) (inventory.cut.depth + 1) index

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit
