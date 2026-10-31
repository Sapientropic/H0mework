import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)

def tag : Epoch.Interface.Tag input depth count := .publicActual prefixLimit renewalLimit oldPast start

def visit := (Epoch.Interface.root input depth count (tag input depth count prefixLimit renewalLimit oldPast start)).initialVisit

/-- Reuse the original common-occurrence factory. Only the law epoch is new;
the instruction positions and financial process are the original ones. -/
def items : List (Epoch.Finance.ActualItem input depth count) :=
  Epoch.Finance.inventory input depth count (tag input depth count prefixLimit renewalLimit oldPast start)
    (visit input depth count prefixLimit renewalLimit oldPast start)

theorem actual_items_are_the_same_public_execution :
    (items input depth count prefixLimit renewalLimit oldPast start).map
      (Epoch.Finance.ActualItem.instruction input depth count) =
      (Physical.Public.execution input depth count prefixLimit renewalLimit oldPast start).items :=
  Epoch.Finance.inventory_is_exact input depth count _ _

theorem no_actual_item_position_is_reused :
    (items input depth count prefixLimit renewalLimit oldPast start).Nodup :=
  Epoch.Finance.inventory_positions_are_not_replayed input depth count _ _

#print axioms actual_items_are_the_same_public_execution
#print axioms no_actual_item_position_is_reused

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
