import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Repair

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ}

def Quiet (current : Current) : Prop := current.technology.holder = none ∧ current.technology.offered = none
instance (current : Current) : Decidable (Quiet current) := by unfold Quiet; infer_instance

def reviewBefore (current : Current) := (law.execute current 0 (word current)).final
def review (current : Current) := Review.produce base scope (reviewBefore current)

def emitAt (current : Current) : List Action :=
  match choose current with
  | some _ => word current
  | none => word current ++ (review current).word

theorem paid_emission_is_the_real_pair (current : Current) (ready : Ready current)
    (chosen : choose current = some ready) : emitAt current = candidate current ready.choice := by
  simp only [emitAt, chosen, paid_word_is_the_selected_pair current ready chosen]

inductive Outcome (current : Current) where
  | private paid (ready : Ready current) (chosen : choose current = some ready)
      (emitted : emitAt current = candidate current ready.choice)
      (recognized : ∀ tail, (grantsAt base scope current (candidate current ready.choice ++ tail)).isEmpty = false)
  | private blocked (absent : choose current = none)
      (all : ∀ choice ∈ choices, ¬ Legal current choice)
      (actual : ∃ refusal, refusal ∈ refusals current)
      (supplied : List (SupplyEvent current)) (exact_supplies : supplied = supplies current)
      (revision : Review.Outcome base scope (reviewBefore current)) (exact_revision : revision = review current)
      (emitted : emitAt current = word current ++ revision.word)

def produce (current : Current) : Outcome current :=
  match chosen : choose current with
  | some ready => .paid ready chosen (paid_emission_is_the_real_pair current ready chosen)
      (fun tail => legal_pair_has_an_actual_grant current ready.choice tail ready.legal)
  | none => .blocked chosen (no_choice_refuses_every_generated_pair current chosen)
      (every_blocked_core_retains_an_actual_guard_failure current chosen)
      (supplies current) rfl (review current) rfl (by simp only [emitAt, chosen])

theorem blocked_attempt_keeps_the_real_refusal (current : Current) (blocked : choose current = none)
    (refusal : Refusal current) : refusal.item ∈ law.rawItems current (emitAt current) ∧
      ¬ law.Valid refusal.item.before refusal.item.request := by
  refine ⟨?_, refusal.refused⟩
  simp only [emitAt, blocked, word, RawLaw.rawItems]
  rw [law.execute_append, law.execute_append]
  exact List.mem_append_left _ (List.mem_append_left _ refusal.actual)

theorem every_supply_is_in_the_emitted_word (current : Current) (event : SupplyEvent current)
    (inside : event ∈ supplies current) : event.item ∈ law.rawItems current (emitAt current) := by
  have actual := every_supply_is_in_the_original_word current event inside
  unfold emitAt
  split
  · exact actual
  · unfold RawLaw.rawItems at actual ⊢
    rw [law.execute_append]
    exact List.mem_append_left _ actual

def continuation (inventory : Joint.Inventory fuel) :=
  ((source fuel).decideAt
    (law.execute inventory.cut.past.frame.raw 0 (emitAt inventory.cut.past.frame.raw)).final
    inventory.cut.past.frame.payments).word

def emit (inventory : Joint.Inventory fuel) : List Action :=
  if Quiet inventory.cut.past.frame.raw then emitAt inventory.cut.past.frame.raw ++ continuation inventory else Exit.emit inventory

def advance (inventory : Joint.Inventory fuel) := Joint.submit inventory (emit inventory)

def run (inventory : Joint.Inventory fuel) : Nat → Joint.Inventory fuel
  | 0 => inventory
  | count + 1 => advance (run inventory count)

def alternate (inventory : Joint.Inventory fuel) : List (List Action) → Joint.Inventory fuel
  | [] => inventory
  | word :: tail => alternate (Joint.submit (advance inventory) word) tail

def descendants {start : Joint.Inventory fuel} {original : Joint.Row start.cut} {inventory : Joint.Inventory fuel}
    (descendant : Joint.Descendant original inventory) : (words : List (List Action)) → Joint.Descendant original (alternate inventory words)
  | [] => descendant
  | word :: tail => descendants ((descendant.step (emit inventory)).step word) tail

def every_old_responsibility_survives (inventory : Joint.Inventory fuel) (row : Joint.Row inventory.cut)
    (inside : row ∈ inventory.frame.rows) (words : List (List Action)) : Joint.Descendant row (alternate inventory words) :=
  descendants (Joint.begin inventory row inside) words

theorem active_emission_is_the_existing_exit (inventory : Joint.Inventory fuel)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) : emit inventory = Exit.emit inventory := by
  have notQuiet : ¬ Quiet inventory.cut.past.frame.raw := by
    rintro ⟨holder, offered⟩
    rcases active with active | active <;> simp_all
  simp only [emit, if_neg notQuiet]

abbrev inputs (inventory : Joint.Inventory fuel) := branchInputs inventory.cut (emit inventory)
abbrev native (inventory : Joint.Inventory fuel) := Runtime.generate fuel (inputs inventory) inventory.cut.depth
abbrev newGrants (inventory : Joint.Inventory fuel) := grantsAt base scope
  (Runtime.mandateCurrentAt fuel (inputs inventory) (inventory.cut.depth + 1))
  (Runtime.mandateWordAt fuel (inputs inventory) (inventory.cut.depth + 1))

theorem new_current_and_word (inventory : Joint.Inventory fuel) :
    Runtime.mandateCurrentAt fuel (inputs inventory) (inventory.cut.depth + 1) = inventory.cut.past.frame.raw ∧
    Runtime.mandateWordAt fuel (inputs inventory) (inventory.cut.depth + 1) = emit inventory := by
  exact ⟨new_input_uses_the_original_cut inventory.cut _, new_input_is_actually_emitted inventory.cut _⟩

theorem selected_pair_creates_a_new_native_grant (inventory : Joint.Inventory fuel)
    (quiet : Quiet inventory.cut.past.frame.raw) (ready : Ready inventory.cut.past.frame.raw)
    (chosen : choose inventory.cut.past.frame.raw = some ready) : (newGrants inventory).isEmpty = false := by
  unfold newGrants
  rw [(new_current_and_word inventory).1, (new_current_and_word inventory).2]
  rw [emit, if_pos quiet, paid_emission_is_the_real_pair _ ready chosen]
  exact legal_pair_has_an_actual_grant _ ready.choice (continuation inventory) ready.legal

theorem every_new_grant_is_in_the_same_native_records (inventory : Joint.Inventory fuel)
    (grant : Grant base scope (Runtime.mandateCurrentAt fuel (inputs inventory) (inventory.cut.depth + 1))
      (Runtime.mandateWordAt fuel (inputs inventory) (inventory.cut.depth + 1)))
    (actual : grant ∈ newGrants inventory) :
    (⟨⟨inventory.cut.depth + 1, by omega⟩,
      Runtime.traceGrant fuel (inputs inventory) (inventory.cut.depth + 1) (inventory.cut.depth + 1) grant⟩ :
      Sigma fun birth : Fin (inventory.cut.depth + 2) => Runtime.TracedGrant fuel (inputs inventory) birth.val (inventory.cut.depth + 1)) ∈
      (native inventory).mandates := Runtime.every_original_grant_is_retained fuel (inputs inventory) (inventory.cut.depth + 1) ⟨inventory.cut.depth + 1, by omega⟩ grant actual


inductive Receipt (inventory : Joint.Inventory fuel) where
  | private fresh (quiet : Quiet inventory.cut.past.frame.raw)
      (emitted : emit inventory = emitAt inventory.cut.past.frame.raw ++ continuation inventory)
      (outcome : Outcome inventory.cut.past.frame.raw) (exact : outcome = produce inventory.cut.past.frame.raw)
  | private active (notQuiet : ¬ Quiet inventory.cut.past.frame.raw)
      (emitted : emit inventory = Exit.emit inventory)
      (outcome : Exit.Receipt inventory) (exact : outcome = Exit.generate inventory)

def generate (inventory : Joint.Inventory fuel) : Receipt inventory :=
  if quiet : Quiet inventory.cut.past.frame.raw then
    .fresh quiet (by simp only [emit, if_pos quiet]) (produce _) rfl
  else .active quiet (by simp only [emit, if_neg quiet]) (Exit.generate inventory) rfl

theorem every_active_pending_row_keeps_actual_progress (inventory : Joint.Inventory fuel)
    (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) (pending : row.isPending = true) :
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (Joint.carry inventory (emit inventory) row inside).thread.history.state.current.history.map LifecycleEvent.kind := by
  rw [active_emission_is_the_existing_exit inventory active]
  exact Exit.every_active_pending_row_keeps_actual_progress inventory row inside active pending

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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission
