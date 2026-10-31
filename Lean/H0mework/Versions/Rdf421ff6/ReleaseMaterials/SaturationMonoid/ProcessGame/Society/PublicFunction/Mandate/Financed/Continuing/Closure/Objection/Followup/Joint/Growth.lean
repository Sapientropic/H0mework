import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Classification

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ} {inputs : List (List Action)} {cut : Cut fuel inputs}

/-- Count actual native history entries and retained responsibility addresses. -/
def Row.volume (row : Row cut) := row.2.history.state.current.history.length + 1

def volume (rows : List (Row cut)) := (rows.map Row.volume).sum

theorem volume_append (first second : List (Row cut)) :
    volume (first ++ second) = volume first + volume second := by
  simp only [volume, List.map_append, List.sum_append]

theorem Row.receive_volume (row : Row cut) (event : Event cut) :
    row.volume ≤ (row.receive event).volume := by
  have same := (row.2.receiveRun event).history_eq
  change row.2.history.state.current.history.length + 1 ≤
    (row.2.receive event).history.state.current.history.length + 1
  rw [same, List.length_append]
  omega

theorem receive_rows_volume (rows : List (Row cut)) (event : Event cut) :
    volume rows ≤ volume (rows.map (fun row => row.receive event)) := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
      simpa only [volume, List.map_cons, List.sum_cons] using Nat.add_le_add (row.receive_volume event) ih

theorem receive_rows_strict_volume (rows : List (Row cut)) (event : Event cut) (row : Row cut)
    (inside : row ∈ rows) (strict : row.volume < (row.receive event).volume) :
    volume rows < volume (rows.map (fun row => row.receive event)) := by
  induction rows with
  | nil => cases inside
  | cons head tail ih =>
      rcases List.mem_cons.mp inside with same | later
      · subst head
        simpa only [volume, List.map_cons, List.sum_cons] using
          Nat.add_lt_add_of_lt_of_le strict (receive_rows_volume tail event)
      · simpa only [volume, List.map_cons, List.sum_cons] using
          Nat.add_lt_add_of_le_of_lt (head.receive_volume event) (ih later)

theorem Frame.step_volume (frame : Frame cut) (event : Event cut) :
    volume frame.rows ≤ volume (frame.step event).rows := by
  change volume frame.rows ≤ volume (frame.rows.map (fun row => row.receive event) ++ _)
  rw [volume_append]
  exact Nat.le_trans (receive_rows_volume frame.rows event) (Nat.le_add_right _ _)

theorem Frame.fold_volume (frame : Frame cut) (events : List (Event cut)) :
    volume frame.rows ≤ volume (frame.fold events).rows := by
  induction events generalizing frame with
  | nil => rfl
  | cons event tail ih => exact (frame.step_volume event).trans (ih (frame.step event))

theorem a_real_reconfirmation_strictly_grows_its_native_row (row : Row cut) (event : Event cut)
    (reconfirmed : row.canReconfirm event = true) : row.volume < (row.receive event).volume := by
  rcases row with ⟨origin, thread⟩
  rcases thread with ⟨history, within⟩
  cases history with
  | closed state archive slots => cases reconfirmed
  | pending target state slots =>
      change (Cross.readReconfirmation target event.val).isSome = true at reconfirmed
      let receipt := (Cross.readReconfirmation target event.val).get reconfirmed
      have decoded : Cross.readReconfirmation target event.val = some receipt := (Option.some_get _).symm
      change state.current.history.length + 1 <
        ((Cross.History.pending target state slots).receive event.val).state.current.history.length + 1
      simp only [Cross.History.receive, decoded, Cross.History.state,
        NativeResponsibilityProcess.GeneratedState.step, NativeResponsibilityProcess.Edge.target,
        List.length_append, List.length_singleton]
      omega

theorem a_fresh_actual_signature_strictly_grows_the_frame (frame : Frame cut) (event : Event cut)
    (claim : Claim fuel inputs) (decoded : read fuel inputs event.val = some claim)
    (fresh : eventKey event ∉ frame.seen) : volume frame.rows < volume (frame.step event).rows := by
  rcases every_fresh_signature_continues_an_actual_row_or_admits_a_native_row
    frame.rows frame.seen event claim decoded fresh with continued | admitted
  · obtain ⟨_, ⟨row, inside, reaffirmed⟩, _⟩ := continued
    have strict := receive_rows_strict_volume frame.rows event row inside
      (a_real_reconfirmation_strictly_grows_its_native_row row event reaffirmed)
    change volume frame.rows < volume (frame.rows.map (fun row => row.receive event) ++ _)
    rw [volume_append]
    exact lt_of_lt_of_le strict (Nat.le_add_right _ _)
  · obtain ⟨_, row, born⟩ := admitted
    change volume frame.rows < volume (frame.rows.map (fun row => row.receive event) ++ _)
    rw [volume_append, born]
    simp only [Option.toList_some, volume, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have mono := receive_rows_volume frame.rows event
    dsimp only [volume] at mono
    have positive : 0 < row.volume := Nat.zero_lt_succ _
    omega

theorem before_volume (inventory : Inventory fuel) (word : List Action) :
    volume (before inventory word).rows = volume inventory.frame.rows := by
  unfold before volume
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro row _
  exact congrArg (fun state => state.current.history.length + 1) (row.2.transport_state word)

theorem submitting_never_erases_native_volume (inventory : Inventory fuel) (word : List Action) :
    volume inventory.frame.rows ≤ volume (submit inventory word).frame.rows := by
  rw [← before_volume inventory word]
  exact Frame.fold_volume _ _

theorem an_actual_signature_strictly_grows_the_whole_native_ledger (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) (claim : Claim fuel (submit inventory word).inputs)
    (decoded : read fuel (submit inventory word).inputs ((actualEvents inventory.cut word).get index).val = some claim) :
    volume inventory.frame.rows < volume (submit inventory word).frame.rows := by
  have preceding :=  Frame.fold_volume (before inventory word) ((actualEvents inventory.cut word).take index.val)
  rw [before_volume] at preceding
  have strict := a_fresh_actual_signature_strictly_grows_the_frame (frameBefore inventory word index.val)
    ((actualEvents inventory.cut word).get index) claim decoded (actual_event_is_fresh inventory word index)
  have tail := Frame.fold_volume
    ((frameBefore inventory word index.val).step ((actualEvents inventory.cut word).get index))
    ((actualEvents inventory.cut word).drop (index.val + 1))
  change volume inventory.frame.rows < volume (after inventory word).rows
  rw [after_splits_at_the_actual_event inventory word index]
  exact lt_of_lt_of_le (lt_of_le_of_lt preceding strict) tail

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
