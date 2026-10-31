import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Signature

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup

variable {fuel : ℚ}

inductive Outcome (current : Current) (actor : Bool) where
  | private paid (ready : Ready current actor) (chosen : choose current actor = some ready)
      (emitted : word current actor = candidate current actor ready.method ++ [submission])
      (actual : law.Valid (beforeRenewal current actor ready.method) (renewal current actor ready.method))
      (effect : (law.step (beforeRenewal current actor ready.method) (renewal current actor ready.method)).technology =
        Mandate.advance scope (beforeRenewal current actor ready.method) .renew)
  | private blocked (absent : choose current actor = none)
      (all : ∀ method ∈ methods, ¬ Legal current actor method)
      (actual : ∃ refusal, refusal ∈ refusals current actor)
      (supplied : List (SupplyEvent current actor)) (exact_supplies : supplied = supplies current actor)

def produce (current : Current) (actor : Bool) : Outcome current actor :=
  match chosen : choose current actor with
  | some ready => .paid ready chosen (by rw [word, paid_prefix_is_the_selected_pair current actor ready chosen])
      (paid_renewal_is_a_real_second_command current actor ready)
      (paid_renewal_advances_the_actual_authority current actor ready)
  | none => .blocked chosen (no_choice_refuses_every_generated_method current actor chosen)
      (every_blocked_core_retains_an_actual_guard_failure current actor chosen) (supplies current actor) rfl

def pending (inventory : Joint.Inventory fuel) := inventory.frame.rows.any Joint.Row.isPending

/-- A pending withdrawal owns the next response. Renewal cannot replace its snapshot. -/
def emit (inventory : Joint.Inventory fuel) : List Action :=
  if pending inventory then Admission.emit inventory
  else match inventory.cut.past.frame.raw.technology.holder with
    | some actor => word inventory.cut.past.frame.raw actor
    | none => Admission.emit inventory

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

inductive Receipt (inventory : Joint.Inventory fuel) where
  | private renewal (actor : Bool) (held : inventory.cut.past.frame.raw.technology.holder = some actor)
      (clear : pending inventory = false) (emitted : emit inventory = word inventory.cut.past.frame.raw actor)
      (outcome : Outcome inventory.cut.past.frame.raw actor) (exact : outcome = produce inventory.cut.past.frame.raw actor)
      (claim : Claim fuel (branchInputs inventory.cut (word inventory.cut.past.frame.raw actor)))
      (read : Objection.read fuel _ (signaturePosition inventory.cut actor) = some claim)
      (snapshot : claim.snapshot = (law.execute inventory.cut.past.frame.raw 0 (attemptedWord inventory.cut.past.frame.raw actor)).final.technology)
  | private existing (emitted : emit inventory = Admission.emit inventory)
      (outcome : Admission.Receipt inventory) (exact : outcome = Admission.generate inventory)

def generate (inventory : Joint.Inventory fuel) : Receipt inventory :=
  if waiting : pending inventory then
    .existing (by simp only [emit, if_pos waiting]) (Admission.generate inventory) rfl
  else match held : inventory.cut.past.frame.raw.technology.holder with
    | some actor => .renewal actor held (Bool.eq_false_iff.mpr waiting)
        (by simp only [emit, if_neg waiting, held]) (produce _ actor) rfl
        (signature inventory.cut actor held) (signature_is_actually_read inventory.cut actor held)
        (signature_snapshot_is_after_the_actual_attempt inventory.cut actor held)
    | none => .existing (by simp only [emit, if_neg waiting, held]) (Admission.generate inventory) rfl

theorem every_active_pending_row_keeps_actual_progress (inventory : Joint.Inventory fuel)
    (row : Joint.Row inventory.cut) (inside : row ∈ inventory.frame.rows)
    (active : Mandate.Response.Active inventory.cut.past.frame.raw) (waiting : row.isPending = true) :
    (row.2.history.state.current.history.map LifecycleEvent.kind ++ [.progressed]) <+:
      (Joint.carry inventory (emit inventory) row inside).thread.history.state.current.history.map LifecycleEvent.kind := by
  have pending : pending inventory = true := List.any_eq_true.mpr ⟨row, inside, waiting⟩
  rw [emit, if_pos pending]
  exact Admission.every_active_pending_row_keeps_actual_progress inventory row inside active waiting

abbrev inputs (inventory : Joint.Inventory fuel) := branchInputs inventory.cut (emit inventory)
abbrev native (inventory : Joint.Inventory fuel) := Runtime.generate fuel (inputs inventory) inventory.cut.depth

theorem new_current_and_word (inventory : Joint.Inventory fuel) :
    Runtime.mandateCurrentAt fuel (inputs inventory) (inventory.cut.depth + 1) = inventory.cut.past.frame.raw ∧
    Runtime.mandateWordAt fuel (inputs inventory) (inventory.cut.depth + 1) = emit inventory :=
  ⟨new_input_uses_the_original_cut inventory.cut _, new_input_is_actually_emitted inventory.cut _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal
