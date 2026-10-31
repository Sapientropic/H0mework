import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Cost.Local

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

theorem every_complete_original_programme_pays_strictly_more_than_the_floor
    (code : Programme.Submission (Party := Bool) (Good := Bool) (Port := Unit) (Technology := Nat) (Instrument := Unit))
    (cleared : RawCleared code) : 1 < Cost.value reading input before code := by
  obtain ⟨item,listed,production⟩ := every_complete_original_debt_clearing_contains_an_actual_productive_item code cleared
  have accepted := every_actual_programme_inventory_item_is_accepted before code item listed
  have paid := (the_productive_item_pays_its_actual_input_and_positive_maintenance item production accepted).1
  have lower := an_original_nonnegative_member_is_bounded_by_the_whole_sum (Programme.items input before code) item listed
  have strict : 1 < Cost.itemValue reading law item := by rw [paid]; linarith [epsilon_positive item.before.technology]
  have bound : Cost.itemValue reading law item ≤ Cost.value reading input before code := by
    simpa only [Cost.value,the_active_physical_interpreter_is_the_same_source_law,reading,zero_mul,add_zero] using lower
  exact strict.trans_le bound

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
