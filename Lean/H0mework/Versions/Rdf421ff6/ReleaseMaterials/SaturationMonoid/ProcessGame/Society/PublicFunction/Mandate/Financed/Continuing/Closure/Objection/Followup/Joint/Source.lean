import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Keys
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {fuel : ℚ} {inputs : List (List Action)}

def eventsBefore (cut : Cut fuel inputs) : List (Event cut) :=
  (Response.positionsBefore (fuel := fuel) (inputs := inputs) (cut.depth + 2)).attach.map fun position =>
    ⟨position.val, Response.position_before position.val position.property⟩

def seedAt (cut : Cut fuel inputs) (event : Event cut) : Option (Row cut) :=
  match decoded : read fuel inputs event.val with
  | none => none
  | some claim => some (seed cut claim (by rw [Response.read_position event.val claim decoded]; exact event.property))

def seedFrame (cut : Cut fuel inputs) : Frame cut :=
  let rows := (eventsBefore cut).filterMap (seedAt cut)
  ⟨rows, rows.map (fun row => originKey row.1)⟩

theorem afterInput_depth (cut : Cut fuel inputs) (word : List Action) : (afterInput cut word).depth = cut.depth + 1 :=
  branchInputs_length cut word

def actualEvent (cut : Cut fuel inputs) (word : List Action)
    (index : Fin (Registered.traceItems (I fuel (branchInputs cut word))
      (ProgrammeHistory.visitAt (I fuel (branchInputs cut word)) (cut.depth + 2)).current).length) : Event (afterInput cut word) :=
  ⟨⟨cut.depth + 2, index⟩, by change cut.depth + 2 < (afterInput cut word).depth + 2; rw [afterInput_depth]; omega⟩

def actualEvents (cut : Cut fuel inputs) (word : List Action) : List (Event (afterInput cut word)) :=
  (List.finRange _).map (actualEvent cut word)

theorem actual_event_key (cut : Cut fuel inputs) (word : List Action) (index : Fin (actualEvents cut word).length) :
    eventKey ((actualEvents cut word).get index) = (cut.depth + 2, index.val) := by
  let count := (Registered.traceItems (I fuel (branchInputs cut word))
    (ProgrammeHistory.visitAt (I fuel (branchInputs cut word)) (cut.depth + 2)).current).length
  have bound : index.val < (List.finRange count).length := by
    simpa only [actualEvents, List.length_map] using index.isLt
  change eventKey (((List.finRange count).map (actualEvent cut word))[index.val]) = _
  rw [List.getElem_map]
  change (cut.depth + 2, ((List.finRange count)[index.val]'bound).val) = _
  simp only [List.getElem_finRange]
  rfl

theorem seed_keys_before (cut : Cut fuel inputs) : (seedFrame cut).KeysBefore (cut.depth + 2, 0) := by
  intro key present
  obtain ⟨row, inside, same⟩ := List.mem_map.mp present
  cases same
  obtain ⟨event, _, selected⟩ := List.mem_filterMap.mp inside
  unfold seedAt at selected
  split at selected
  · cases selected
  · rename_i claim decoded
    cases Option.some.inj selected
    exact Or.inl (by change claim.position.ordinal < cut.depth + 2; rw [Response.read_position event.val claim decoded]; exact event.property)

structure Inventory (fuel : ℚ) where
  private mk ::
  inputs : List (List Action)
  cut : Cut fuel inputs
  frame : Frame cut
  covered : frame.CoversOrigins
  keys_before : frame.KeysBefore (cut.depth + 2, 0)

def initial (cut : Cut fuel inputs) : Inventory fuel :=
  ⟨inputs, cut, seedFrame cut, fun row inside => List.mem_map.mpr ⟨row, inside, rfl⟩, seed_keys_before cut⟩

def emit (inventory : Inventory fuel) : List Action :=
  if inventory.frame.rows.any Row.matches then Response.word inventory.cut.past.frame.raw
  else if inventory.frame.rows.any Row.isPending then [submission]
  else (reply fuel inventory.cut.past).word

def before (inventory : Inventory fuel) (word : List Action) : Frame (afterInput inventory.cut word) :=
  ⟨inventory.frame.rows.map (fun row => row.transport word), inventory.frame.seen⟩

def after (inventory : Inventory fuel) (word : List Action) :=
  (before inventory word).fold (actualEvents inventory.cut word)

theorem before_covers_origins (inventory : Inventory fuel) (word : List Action) : (before inventory word).CoversOrigins := by
  intro row present
  obtain ⟨old, inside, same⟩ := List.mem_map.mp present
  cases same
  exact inventory.covered old inside

theorem after_keys_before (inventory : Inventory fuel) (word : List Action) :
    (after inventory word).KeysBefore ((afterInput inventory.cut word).depth + 2, 0) := by
  apply Frame.fold_keys_before
  · intro key present
    have old := inventory.keys_before key present
    rw [afterInput_depth]
    rcases old with earlier | ⟨_, impossible⟩
    · exact Or.inl (by dsimp at earlier ⊢; omega)
    · exact False.elim (Nat.not_lt_zero _ impossible)
  · intro event present
    obtain ⟨index, _, same⟩ := List.mem_map.mp present
    cases same
    exact Or.inl (by simp only [eventKey, actualEvent, afterInput_depth]; omega)

def submit (inventory : Inventory fuel) (word : List Action) : Inventory fuel :=
  ⟨branchInputs inventory.cut word, afterInput inventory.cut word, after inventory word,
    (before inventory word).fold_covers_origins (before_covers_origins inventory word) _, after_keys_before inventory word⟩

def advance (inventory : Inventory fuel) := submit inventory (emit inventory)

def run (inventory : Inventory fuel) : Nat → Inventory fuel
  | 0 => inventory
  | count + 1 => advance (run inventory count)

def alternate (inventory : Inventory fuel) : List (List Action) → Inventory fuel
  | [] => inventory
  | word :: tail => alternate (submit (advance inventory) word) tail

def frameBefore (inventory : Inventory fuel) (word : List Action) (index : Nat) :=
  (before inventory word).fold ((actualEvents inventory.cut word).take index)

theorem actual_event_is_fresh (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) :
    eventKey ((actualEvents inventory.cut word).get index) ∉ (frameBefore inventory word index.val).seen := by
  have ordered : (frameBefore inventory word index.val).KeysBefore (inventory.cut.depth + 2, index.val) := by
    apply Frame.fold_keys_before
    · intro key present
      rcases inventory.keys_before key present with earlier | ⟨_, impossible⟩
      · exact Or.inl earlier
      · exact False.elim (Nat.not_lt_zero _ impossible)
    · intro event present
      obtain ⟨number, bound, same⟩ := List.mem_iff_getElem.mp present
      have earlier := Nat.lt_of_lt_of_le bound (List.length_take_le index.val (actualEvents inventory.cut word))
      have full := Nat.lt_of_lt_of_le bound (List.length_take_le' index.val (actualEvents inventory.cut word))
      have original : (actualEvents inventory.cut word).get ⟨number, full⟩ = event := by
        simpa only [List.get_eq_getElem, List.getElem_take] using same
      rw [← original, actual_event_key]
      exact Or.inr ⟨rfl, earlier⟩
  intro repeated
  have impossible := ordered _ repeated
  rw [actual_event_key] at impossible
  rcases impossible with earlier | ⟨_, earlier⟩ <;> exact Nat.lt_irrefl _ earlier

def decisionAt (inventory : Inventory fuel) (word : List Action) (index : Fin (actualEvents inventory.cut word).length) :=
  decide (frameBefore inventory word index.val).rows (frameBefore inventory word index.val).seen ((actualEvents inventory.cut word).get index)

theorem eventsBefore_covers_every_original_position (cut : Cut fuel inputs) (event : Event cut) : event ∈ eventsBefore cut := by
  have inside : event.val ∈ Response.positionsBefore (cut.depth + 2) := by
    apply List.mem_flatMap.mpr
    refine ⟨event.val.ordinal, List.mem_range.mpr event.property, ?_⟩
    exact List.mem_map.mpr ⟨event.val.index, List.mem_finRange _, rfl⟩
  exact List.mem_map.mpr ⟨⟨event.val, inside⟩, List.mem_attach _ _, rfl⟩

theorem every_old_actual_claim_is_seeded (cut : Cut fuel inputs) (event : Event cut)
    (inside : event ∈ eventsBefore cut) (claim : Claim fuel inputs)
    (decoded : read fuel inputs event.val = some claim) :
    ∃ row ∈ (seedFrame cut).rows, row.1 = (⟨inputs, claim⟩ : Origin fuel) := by
  let row := seed cut claim (by rw [Response.read_position event.val claim decoded]; exact event.property)
  refine ⟨row, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  refine ⟨event, inside, ?_⟩
  unfold seedAt
  split
  · rename_i absent
    rw [decoded] at absent
    cases absent
  · rename_i actual same
    have equal : actual = claim := Option.some.inj (same.symm.trans decoded)
    subst actual
    rfl

theorem actual_word_uses_the_inventory_cut (inventory : Inventory fuel) (word : List Action) :
    (actualExecution fuel (submit inventory word).inputs (inventory.cut.depth + 1)).submitted = word ∧
    (actualExecution fuel (submit inventory word).inputs (inventory.cut.depth + 1)).before = inventory.cut.past.frame.raw :=
  ⟨new_input_is_actually_emitted inventory.cut word, new_input_uses_the_original_cut inventory.cut word⟩

theorem next_is_the_actual_effect (inventory : Inventory fuel) (word : List Action) :
    (submit inventory word).cut.past = inventory.cut.past.append word :=
  afterInput_is_the_interpreted_original_cut inventory.cut word

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
