import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window

open Abolition.Root Abolition.Root.Registered PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- Once the original window has been missed, no later programme can
backdate either the old material debits or any new ones. -/
def later_actions_cannot_backdate_an_original_missed_service
    (source : C) (task : PublicTaskSpec Party Good) (before after : Script)
    (alreadyLate : task.deadline < (Execution.endAt source before).raw.clock)
    (allLate : ∀ receipt ∈ Execution.timedInventory source before, task.deadline < receipt.2) :
    Shortage source task (before ++ after) := by
  apply material_committed_after_the_deadline_leaves_the_original_service_unpaid
  intro ordinal
  have present : Execution.timedAt source (before ++ after) ordinal ∈
      Execution.timedInventory source (before ++ after) := by
    unfold Execution.timedAt
    exact List.get_mem _ _
  rw [Execution.timedInventory_append] at present
  rcases List.mem_append.mp present with old | later
  · exact allLate _ old
  · have actual := Execution.every_original_service_commits_between_source_and_terminal_clock _ _ _ later
    exact alreadyLate.trans_le actual.1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Window
