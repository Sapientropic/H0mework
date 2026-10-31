import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Row

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs}

abbrev PositionKey := Nat × Nat

def eventKey (event : Event cut) : PositionKey := ⟨event.val.ordinal, event.val.index.val⟩

def originKey (origin : Origin fuel) : PositionKey := ⟨origin.2.position.ordinal, origin.2.position.index.val⟩

inductive Decision (rows : List (Row cut)) (seen : List PositionKey) (event : Event cut)
  | ordinary (absent : read fuel inputs event.val = none)
  | known (claim : Claim fuel inputs) (decoded : read fuel inputs event.val = some claim)
      (repeated : eventKey event ∈ seen)
  | continued (claim : Claim fuel inputs) (decoded : read fuel inputs event.val = some claim)
      (fresh : eventKey event ∉ seen) (existing : rows.any (fun row => row.canReconfirm event) = true)
  | admitted (claim : Claim fuel inputs) (decoded : read fuel inputs event.val = some claim)
      (fresh : eventKey event ∉ seen) (noExisting : rows.any (fun row => row.canReconfirm event) = false)

def decide (rows : List (Row cut)) (seen : List PositionKey) (event : Event cut) : Decision rows seen event :=
  match decoded : read fuel inputs event.val with
  | none => .ordinary decoded
  | some claim =>
      if repeated : eventKey event ∈ seen then .known claim decoded repeated
      else match checked : rows.any (fun row => row.canReconfirm event) with
        | true => .continued claim decoded repeated checked
        | false => .admitted claim decoded repeated checked

inductive Mode
  | ordinary | known | continued | admitted
  deriving DecidableEq

def Decision.mode {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut} : Decision rows seen event → Mode
  | .ordinary .. => .ordinary | .known .. => .known | .continued .. => .continued | .admitted .. => .admitted

def Decision.claim? {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut} :
    Decision rows seen event → Option (Claim fuel inputs)
  | .ordinary .. => none
  | .known claim .. | .continued claim .. | .admitted claim .. => some claim

def Decision.newborn {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut} :
    Decision rows seen event → Option (Row cut)
  | .admitted claim decoded _ _ => some (birth cut claim (by
      rw [Response.read_position event.val claim decoded]
      exact event.property))
  | _ => none

def Decision.nextSeen {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut} : Decision rows seen event → List PositionKey
  | .continued .. | .admitted .. => seen ++ [eventKey event]
  | _ => seen

theorem every_decoded_signature_is_accounted (rows : List (Row cut)) (seen : List PositionKey) (event : Event cut)
    (claim : Claim fuel inputs) (decoded : read fuel inputs event.val = some claim) :
    (decide rows seen event).claim? = some claim := by
  unfold decide
  split
  · rename_i absent
    rw [decoded] at absent
    cases absent
  · rename_i actual same
    have equal : actual = claim := Option.some.inj (same.symm.trans decoded)
    subst actual
    split
    · rfl
    · split <;> rfl

theorem continuation_does_not_admit_again {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut}
    (decision : Decision rows seen event) (continued : decision.mode = .continued) : decision.newborn = none := by
  cases decision <;> first | rfl | cases continued

theorem every_newborn_uses_this_actual_signature {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut}
    (decision : Decision rows seen event) (row : Row cut) (born : decision.newborn = some row) :
    ∃ claim : Claim fuel inputs, read fuel inputs event.val = some claim ∧ row.1 = (⟨inputs, claim⟩ : Origin fuel) ∧
      eventKey event ∉ seen ∧ rows.any (fun row => row.canReconfirm event) = false := by
  cases decision with
  | ordinary absent => cases born
  | known claim decoded repeated => cases born
  | continued claim decoded fresh existing => cases born
  | admitted claim decoded fresh noExisting =>
      cases Option.some.inj born
      exact ⟨claim, decoded, rfl, fresh, noExisting⟩

theorem every_newborn_starts_with_its_own_native_admission {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut}
    (decision : Decision rows seen event) (row : Row cut) (born : decision.newborn = some row) :
    row.2.history.state.current.slots = [.live (obligation fuel row.1.1 row.1.2)] ∧
    row.2.history.state.current.history.map ResponsibilityLifecycle.LifecycleEvent.kind = [.admitted] := by
  cases decision with
  | ordinary absent => cases born
  | known claim decoded repeated => cases born
  | continued claim decoded fresh existing => cases born
  | admitted claim decoded fresh noExisting =>
      cases Option.some.inj born
      exact birth_uses_original_native_admission _ _ _

structure Frame (cut : Cut fuel inputs) where
  rows : List (Row cut)
  seen : List PositionKey

def Frame.step (frame : Frame cut) (event : Event cut) : Frame cut :=
  let decision := decide frame.rows frame.seen event
  ⟨frame.rows.map (fun row => row.receive event) ++ decision.newborn.toList, decision.nextSeen⟩

def Frame.fold (frame : Frame cut) : List (Event cut) → Frame cut
  | [] => frame
  | event :: tail => (frame.step event).fold tail

theorem old_row_is_preserved_at_every_event (frame : Frame cut) (event : Event cut) (row : Row cut)
    (present : row ∈ frame.rows) : row.receive event ∈ (frame.step event).rows := by
  exact List.mem_append_left _ (List.mem_map.mpr ⟨row, present, rfl⟩)

theorem old_row_consumes_the_whole_shared_word (frame : Frame cut) (events : List (Event cut)) (row : Row cut)
    (present : row ∈ frame.rows) : row.follow events ∈ (frame.fold events).rows := by
  induction events generalizing frame row with
  | nil => exact present
  | cons event tail ih => exact ih (frame.step event) (row.receive event) (old_row_is_preserved_at_every_event frame event row present)


def Frame.CoversOrigins (frame : Frame cut) : Prop :=
  ∀ row ∈ frame.rows, originKey row.1 ∈ frame.seen

theorem Decision.old_keys_remain {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut}
    (decision : Decision rows seen event) {key : PositionKey} (present : key ∈ seen) : key ∈ decision.nextSeen := by
  cases decision <;> first | exact present | exact List.mem_append_left _ present

theorem Decision.newborn_key_is_recorded {rows : List (Row cut)} {seen : List PositionKey} {event : Event cut}
    (decision : Decision rows seen event) (row : Row cut) (born : decision.newborn = some row) :
    originKey row.1 ∈ decision.nextSeen := by
  cases decision with
  | ordinary absent => cases born
  | known claim decoded repeated => cases born
  | continued claim decoded fresh existing => cases born
  | admitted claim decoded fresh noExisting =>
      cases Option.some.inj born
      have same := Response.read_position event.val claim decoded
      change (claim.position.ordinal, claim.position.index.val) ∈ seen ++ [eventKey event]
      rw [same]
      exact List.mem_append_right _ (List.mem_singleton_self _)

theorem Frame.step_covers_origins (frame : Frame cut) (covered : frame.CoversOrigins) (event : Event cut) :
    (frame.step event).CoversOrigins := by
  intro row present
  rcases List.mem_append.mp present with old | born
  · obtain ⟨previous, inside, same⟩ := List.mem_map.mp old
    cases same
    exact (decide frame.rows frame.seen event).old_keys_remain (covered previous inside)
  · exact (decide frame.rows frame.seen event).newborn_key_is_recorded row (by simpa only [Option.mem_toList] using born)

theorem Frame.fold_covers_origins (frame : Frame cut) (covered : frame.CoversOrigins) :
    ∀ events, (frame.fold events).CoversOrigins
  | [] => covered
  | event :: tail => (frame.step event).fold_covers_origins (frame.step_covers_origins covered event) tail

theorem no_newborn_reuses_an_original_slot (frame : Frame cut) (covered : frame.CoversOrigins) (event : Event cut)
    (newborn : Row cut) (born : (decide frame.rows frame.seen event).newborn = some newborn)
    (old : Row cut) (inside : old ∈ frame.rows) : originKey newborn.1 ≠ originKey old.1 := by
  obtain ⟨claim, decoded, same, fresh, _⟩ := every_newborn_uses_this_actual_signature _ newborn born
  intro equal
  have recorded := covered old inside
  rw [← equal, same] at recorded
  have position := Response.read_position event.val claim decoded
  change (claim.position.ordinal, claim.position.index.val) ∈ frame.seen at recorded
  rw [position] at recorded
  exact fresh recorded

theorem Frame.fold_append (frame : Frame cut) (first second : List (Event cut)) :
    frame.fold (first ++ second) = (frame.fold first).fold second := by
  induction first generalizing frame with
  | nil => rfl
  | cons event tail ih => exact ih (frame.step event)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
