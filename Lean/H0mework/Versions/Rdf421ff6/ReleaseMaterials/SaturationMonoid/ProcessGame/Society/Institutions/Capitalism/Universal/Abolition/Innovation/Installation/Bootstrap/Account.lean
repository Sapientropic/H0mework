import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Runtime.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

theorem the_closed_original_account_is_the_literal_source_prefix_account (nature : RequestAt) :
    (closedOriginal nature).account = Macro.Inventory.before input 0 count 0 0 0 count
      (firstOriginal nature).snapshot := by
  let frame := closedOriginal nature
  have complete := (Macro.Bound.generated_bookkeeping_completion (firstOriginal nature)).1
  have original := Macro.Continuation.completed_root_account_is_the_literal_next_input_seed
    (review := none) input 0 count 0 0 0 count frame.start frame.proposal frame.sourcePosition frame.cursor
    frame.sourceFold complete
  exact original.trans (congrArg (Macro.Inventory.before input 0 count 0 0 0 count)
    (Macro.Bound.exact_original_inventory_closes_its_own_bookkeeping (firstOriginal nature)).2)

theorem the_original_macro_base_slots_are_the_same_pure_source_financial_cursor :
    (Epoch.Finance.Future.Installed.initial input 0 count 0 count).current.slots =
      (Financial.Installation.Runtime.cursorAt input 0 count).account.current.slots.map
        (Epoch.Finance.Legacy.slot input 0 count) := by
  change (Epoch.Finance.Legacy.generated input 0 count
    ((Financial.Installation.Runtime.frames input 0 count).cursor input).account).current.slots = _
  rw [(Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained input 0 count _).1]
  exact congrArg (fun cursor =>
    cursor.account.current.slots.map (Epoch.Finance.Legacy.slot input 0 count))
    (Financial.Installation.Runtime.frames_cursor input 0 count)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
