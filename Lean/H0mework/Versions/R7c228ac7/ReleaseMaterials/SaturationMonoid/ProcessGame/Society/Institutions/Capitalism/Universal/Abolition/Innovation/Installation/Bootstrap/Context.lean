import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Origin

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_capital_context_has_the_original_physical_index : Settlement.physicalIndex input 0 count = 2 := by
  unfold Settlement.physicalIndex Settlement.oldCursor Settlement.oldFrame
  rw [Financial.Installation.Runtime.frames_cursor]
  exact (Epoch.Finance.Installation.PendingDrain.drain input 0 0).physicalIndex.trans rfl

theorem the_capital_context_reads_the_original_committed_visit :
    Settlement.committedVisit input 0 count = ProgrammeHistory.visitAt input 1 := by
  unfold Settlement.committedVisit
  rw [the_capital_context_has_the_original_physical_index]

theorem the_original_member_inventory_is_generated_before_the_trial :
    Actual.members input 0 count = [0,1,2] := by
  change Settlement.members input 0 count = _
  unfold Settlement.members
  rw [the_capital_context_reads_the_original_committed_visit]
  decide +kernel

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
