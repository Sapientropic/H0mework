import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {fuel : ℚ}

structure Carried (inventory : Inventory fuel) (word : List Action) (row : Row inventory.cut) where
  private mk ::
  thread : Thread row.1 (submit inventory word).cut
  exact_thread : thread = (row.2.transport word).fold (actualEvents inventory.cut word)
  present : (⟨row.1, thread⟩ : Row (submit inventory word).cut) ∈ (submit inventory word).frame.rows
  original_state : (row.2.transport word).history.state = row.2.history.state
  crossing : (Cross.process row.1.2).Run row.2.history.state.current thread.history.state.current
  complete : (Cross.process row.1.2).Run (ResponsibilityState.empty (V fuel row.1.1)) thread.history.state.current

def carry (inventory : Inventory fuel) (word : List Action) (row : Row inventory.cut)
    (inside : row ∈ inventory.frame.rows) : Carried inventory word row := by
  let thread := (row.2.transport word).fold (actualEvents inventory.cut word)
  refine ⟨thread, rfl, ?_, row.2.transport_state word, ?_, thread.history.state.generated⟩
  · exact old_row_consumes_the_whole_shared_word (before inventory word) _ (row.transport word)
      (List.mem_map.mpr ⟨row, inside, rfl⟩)
  · have crossing := (row.2.transport word).foldRun (actualEvents inventory.cut word)
    rw [row.2.transport_state word] at crossing
    exact crossing

theorem after_splits_at_the_actual_event (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) :
    after inventory word =
      ((frameBefore inventory word index.val).step ((actualEvents inventory.cut word).get index)).fold
        ((actualEvents inventory.cut word).drop (index.val + 1)) := by
  have split : actualEvents inventory.cut word =
      (actualEvents inventory.cut word).take index.val ++
        (actualEvents inventory.cut word).get index :: (actualEvents inventory.cut word).drop (index.val + 1) := by
    rw [List.cons_get_drop_succ, List.take_append_drop]
  unfold after
  conv_lhs => rw [split]
  rw [Frame.fold_append]
  rfl

structure BornAt (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) where
  private mk ::
  row : Row (submit inventory word).cut
  admitted : (decisionAt inventory word index).newborn = some row
  native_admission : row.2.history.state.current.slots = [.live (obligation fuel row.1.1 row.1.2)] ∧
    row.2.history.state.current.history.map LifecycleEvent.kind = [.admitted]
  thread : Thread row.1 (submit inventory word).cut
  exact_thread : thread = row.2.fold ((actualEvents inventory.cut word).drop (index.val + 1))
  present : (⟨row.1, thread⟩ : Row (submit inventory word).cut) ∈ (submit inventory word).frame.rows
  crossing : (Cross.process row.1.2).Run row.2.history.state.current thread.history.state.current
  complete : (Cross.process row.1.2).Run (ResponsibilityState.empty (V fuel row.1.1)) thread.history.state.current

def newbornAt (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) : Option (BornAt inventory word index) :=
  match born : (decisionAt inventory word index).newborn with
  | none => none
  | some row => some ⟨row, born, every_newborn_starts_with_its_own_native_admission _ row born, row.2.fold ((actualEvents inventory.cut word).drop (index.val + 1)), rfl, by
      change row.follow ((actualEvents inventory.cut word).drop (index.val + 1)) ∈ (after inventory word).rows
      rw [after_splits_at_the_actual_event inventory word index]
      apply old_row_consumes_the_whole_shared_word
      exact List.mem_append_right _ (by simpa only [Option.mem_toList, decisionAt] using born),
      row.2.foldRun _, (row.2.fold _).history.state.generated⟩

theorem newbornAt_is_complete (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) (row : Row (submit inventory word).cut)
    (born : (decisionAt inventory word index).newborn = some row) :
    (newbornAt inventory word index).isSome = true := by
  unfold newbornAt
  split
  · rename_i absent
    rw [born] at absent
    cases absent
  · rfl

theorem current_prefix_covers_origins (inventory : Inventory fuel) (word : List Action) (index : Nat) :
    (frameBefore inventory word index).CoversOrigins :=
  (before inventory word).fold_covers_origins (before_covers_origins inventory word) _

theorem actual_newborn_never_duplicates_an_old_origin (inventory : Inventory fuel) (word : List Action)
    (index : Fin (actualEvents inventory.cut word).length) (newborn old : Row (submit inventory word).cut)
    (born : (decisionAt inventory word index).newborn = some newborn)
    (inside : old ∈ (frameBefore inventory word index.val).rows) : originKey newborn.1 ≠ originKey old.1 :=
  no_newborn_reuses_an_original_slot _ (current_prefix_covers_origins inventory word index.val) _ newborn born old inside

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Joint
