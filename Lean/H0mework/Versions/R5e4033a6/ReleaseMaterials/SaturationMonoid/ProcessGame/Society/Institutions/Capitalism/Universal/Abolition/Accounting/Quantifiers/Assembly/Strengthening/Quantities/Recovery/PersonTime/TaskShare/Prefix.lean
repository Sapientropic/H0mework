import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Observation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare

open Abolition.Root Abolition.Root.Registered

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {origin : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {exposure repair : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

def prefixTask (task : Ordinal origin exposure) : Ordinal origin (exposure ++ repair) :=
  ⟨task.val, by
    rw [Execution.inventory_append, List.length_append]
    exact task.isLt.trans_le (Nat.le_add_right _ _)⟩

theorem prefixTask_reads_the_same_original_timed_item (task : Ordinal origin exposure) :
    Execution.timedAt origin (exposure ++ repair) (prefixTask (repair := repair) task) =
      Execution.timedAt origin exposure task := by
  have existsInPrefix : task.val < (Execution.timedInventory origin exposure).length := by
    rw [← List.length_map Prod.fst, Execution.timedInventory_is_the_original_inventory]
    exact task.isLt
  have wholeRead : some (Execution.timedAt origin (exposure ++ repair) (prefixTask (repair := repair) task)) =
      (Execution.timedInventory origin (exposure ++ repair))[task.val]? := by
    unfold Execution.timedAt
    exact (List.getElem?_eq_getElem _).symm
  rw [Execution.timedInventory_append, List.getElem?_append_left existsInPrefix] at wholeRead
  exact Option.some.inj (wholeRead.trans (List.getElem?_eq_getElem existsInPrefix))

theorem prefixTask_keeps_the_same_original_performer (task : Ordinal origin exposure) (person : Party) :
    ownAction origin (exposure ++ repair) (prefixTask (repair := repair) task) person ↔
      ownAction origin exposure task person := by
  unfold ownAction
  rw [prefixTask_reads_the_same_original_timed_item]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.TaskShare
