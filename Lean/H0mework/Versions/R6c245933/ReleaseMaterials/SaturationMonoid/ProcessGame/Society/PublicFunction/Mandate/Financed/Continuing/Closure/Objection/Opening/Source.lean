import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Material
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Effects
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup

variable {fuel : ℚ}

inductive Outcome (current : Current) where
  | private paid (selected : (select current).isPaid = true)
      (retired : (law.execute current 0 (word current)).final.technology.holder = none ∧
        (law.execute current 0 (word current)).final.technology.offered = none)
  | private repair (selected : (select current).isPaid = false)
      (attempted : ∃ event ∈ supplies current, 0 < event.demand.quantity ∧
        event.item ∈ law.rawItems current (word current))

def outcome (current : Current) (active : Mandate.Response.Active current) : Outcome current :=
  if paid : (select current).isPaid = true then
    .paid paid (a_paid_selected_word_retires_the_actual_authority current paid)
  else .repair (Bool.eq_false_iff.mpr paid)
    (blocked_active_cut_actually_attempts_a_positive_supply current active (Bool.eq_false_iff.mpr paid))

/-- With no active authority, the original joint continuation still owns all
stale responsibilities. Absence of a seat is not a discharge receipt. -/
def emit (inventory : Joint.Inventory fuel) : List Action :=
  if Mandate.Response.Active inventory.cut.past.frame.raw then word inventory.cut.past.frame.raw
  else (reply fuel inventory.cut.past).word

theorem active_emission (inventory : Joint.Inventory fuel) (active : Mandate.Response.Active inventory.cut.past.frame.raw) :
    emit inventory = signedWord (suffix inventory.cut.past.frame.raw) := by
  simp only [emit, if_pos active, word]

structure ActiveReceipt (inventory : Joint.Inventory fuel) where
  private mk ::
  active : Mandate.Response.Active inventory.cut.past.frame.raw
  emitted : emit inventory = signedWord (suffix inventory.cut.past.frame.raw)
  claim : Claim fuel (branchInputs inventory.cut (signedWord (suffix inventory.cut.past.frame.raw)))
  decoded : read fuel _ (signaturePosition inventory.cut (suffix inventory.cut.past.frame.raw)) = some claim
  snapshot : claim.snapshot = inventory.cut.past.frame.raw.technology
  native :
    ((Joint.decisionAt inventory (signedWord (suffix inventory.cut.past.frame.raw))
        (firstIndex inventory (suffix inventory.cut.past.frame.raw))).mode = .continued ∧
      (∃ row ∈ (Joint.frameBefore inventory (signedWord (suffix inventory.cut.past.frame.raw)) 0).rows,
        row.canReconfirm ((Joint.actualEvents inventory.cut (signedWord (suffix inventory.cut.past.frame.raw))).get
          (firstIndex inventory (suffix inventory.cut.past.frame.raw))) = true) ∧
      (Joint.decisionAt inventory (signedWord (suffix inventory.cut.past.frame.raw))
        (firstIndex inventory (suffix inventory.cut.past.frame.raw))).newborn = none) ∨
    ((Joint.decisionAt inventory (signedWord (suffix inventory.cut.past.frame.raw))
        (firstIndex inventory (suffix inventory.cut.past.frame.raw))).mode = .admitted ∧
      (Joint.newbornAt inventory (signedWord (suffix inventory.cut.past.frame.raw))
        (firstIndex inventory (suffix inventory.cut.past.frame.raw))).isSome = true)
  response : Outcome inventory.cut.past.frame.raw
  supply : List (SupplyEvent inventory.cut.past.frame.raw)
  supply_exact : supply = supplies inventory.cut.past.frame.raw

inductive Receipt (inventory : Joint.Inventory fuel) where
  | private active (receipt : ActiveReceipt inventory)
  | private inactive (absent : ¬ Mandate.Response.Active inventory.cut.past.frame.raw)
      (emitted : emit inventory = (reply fuel inventory.cut.past).word)

def generate (inventory : Joint.Inventory fuel) : Receipt inventory :=
  if active : Mandate.Response.Active inventory.cut.past.frame.raw then
    .active ⟨active, active_emission inventory active,
      signature inventory.cut (suffix inventory.cut.past.frame.raw) active,
      signature_is_actually_read inventory.cut (suffix inventory.cut.past.frame.raw) active,
      signature_snapshot_is_the_actual_cut inventory.cut (suffix inventory.cut.past.frame.raw) active,
      actual_signature_is_consumed_as_continuation_or_new_native_admission inventory
        (suffix inventory.cut.past.frame.raw) active,
      outcome inventory.cut.past.frame.raw active, supplies inventory.cut.past.frame.raw, rfl⟩
  else .inactive active (by simp only [emit, if_neg active])

def advance (inventory : Joint.Inventory fuel) := Joint.submit inventory (emit inventory)

def run (inventory : Joint.Inventory fuel) : Nat → Joint.Inventory fuel
  | 0 => inventory
  | count + 1 => advance (run inventory count)

def alternate (inventory : Joint.Inventory fuel) : List (List Action) → Joint.Inventory fuel
  | [] => inventory
  | word :: tail => alternate (Joint.submit (advance inventory) word) tail

def descendants {start : Joint.Inventory fuel} {original : Joint.Row start.cut} {inventory : Joint.Inventory fuel}
    (descendant : Joint.Descendant original inventory) : (count : Nat) → Joint.Descendant original (run inventory count)
  | 0 => descendant
  | count + 1 => (descendants descendant count).step (emit (run inventory count))

def alternatingDescendants {start : Joint.Inventory fuel} {original : Joint.Row start.cut} {inventory : Joint.Inventory fuel}
    (descendant : Joint.Descendant original inventory) : (words : List (List Action)) → Joint.Descendant original (alternate inventory words)
  | [] => descendant
  | word :: tail => alternatingDescendants ((descendant.step (emit inventory)).step word) tail

def every_original_survives_source_openings (inventory : Joint.Inventory fuel) (row : Joint.Row inventory.cut)
    (inside : row ∈ inventory.frame.rows) (words : List (List Action)) : Joint.Descendant row (alternate inventory words) :=
  alternatingDescendants (Joint.begin inventory row inside) words

def every_newborn_survives_source_openings (inventory : Joint.Inventory fuel)
    (index : Fin (Joint.actualEvents inventory.cut (emit inventory)).length)
    (born : Joint.BornAt inventory (emit inventory) index) (words : List (List Action)) :
    Joint.Descendant (⟨born.row.1, born.thread⟩ : Joint.Row (advance inventory).cut) (alternate (advance inventory) words) :=
  alternatingDescendants (Joint.begin (advance inventory) ⟨born.row.1, born.thread⟩ born.present) words

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
