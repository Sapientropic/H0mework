import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Source.Inspection
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Continuation.Installed
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Enter

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (window : Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

def shape := Abolition.Root.Epoch.Finance.Installation.Generated.shape window.input window.depth window.count
def world := (shape window).world window.input window.depth window.count
def translation := (shape window).translation window.input window.depth window.count
def account := Abolition.Root.Epoch.Finance.Legacy.generated window.input window.depth window.count window.account

/-- This is the continuation family of the original installed native shape,
with its actual account; no replacement account or target is an input. -/
def family := Abolition.Root.Epoch.Finance.Future.Installed.accountFamily
  window.input window.depth window.count window.depth window.count .nil (account window) ⟨.nil⟩

theorem family_world_is_the_translated_original_world : (family window).N = world window := rfl

theorem all_original_slots_and_history_are_literal :
    (account window).current.slots = window.account.current.slots.map
      (Abolition.Root.Epoch.Finance.Legacy.slot window.input window.depth window.count) ∧
    (account window).current.history = window.account.current.history.map
      (Abolition.Root.Epoch.Finance.Legacy.lifecycle window.input window.depth window.count) :=
  Abolition.Root.Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained
    window.input window.depth window.count window.account

def enterEvolution := Abolition.Root.Epoch.Finance.Installation.Generated.enterEvolution
  window.input window.depth window.count window.depth window.count

theorem entering_keeps_each_original_claim_and_budget
    (entry : OpenResponsibilityAt (world window)
      ((shape window).mappedSupport window.input window.depth window.count window.frame.visit.current)) :
    ((enterEvolution window).destination entry).1.claim = entry.claim ∧
      ((enterEvolution window).destination entry).1.progressBudget = entry.progressBudget :=
  Abolition.Root.Epoch.Finance.Installation.Generated.entry_preserves_every_original_claim_and_budget
    window.input window.depth window.count window.depth window.count entry

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Native
