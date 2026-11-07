import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_original_physical_seed_is_the_actual_capital_successor :
    Migration.origin input 0 count = Control.Scenario.seed := by
  unfold Migration.origin Continuation.initial Financial.Installation.Runtime.physical
  rw [Financial.Installation.Runtime.frames_cursor]
  change ProgrammeSource.rawCurrent input
    (ProgrammeHistory.visitAt input
      (Financial.Installation.Cursor.physicalVisitIndex input
        (Financial.Installation.Runtime.cursorAt input 0 count))).current = _
  rw [(Epoch.Finance.Installation.PendingDrain.drain input 0 0).physicalIndex]
  rfl

theorem the_empty_physical_past_reads_the_original_seed_without_replaying_finance :
    Physical.stateAt input 0 count 0 0 [] =
      ⟨Control.Scenario.seed, .seeking, Repair.alphabet input Control.Scenario.seed⟩ := by
  change Actual.initial input 0 count = _
  unfold Actual.initial
  dsimp only [Actual.origin]
  rw [the_original_physical_seed_is_the_actual_capital_successor]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
