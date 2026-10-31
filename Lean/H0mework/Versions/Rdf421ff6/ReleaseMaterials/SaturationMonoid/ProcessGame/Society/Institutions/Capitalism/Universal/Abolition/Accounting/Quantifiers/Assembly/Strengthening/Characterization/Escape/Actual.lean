import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Material
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.Readings

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
open Abolition.Completion.Actual.Dividend
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (n : Nat)

theorem all_real_epoch_supplements_are_in_the_same_full_material_account
    (party : Party) (good : Good) :
    (Evolving.Epoch.History.currentAt source n).raw.stock party good +
        (Physical.Public.interpreter source.native.input).totalDebit (Optimality.Programme.Epoch.inventory source n) party good =
      source.raw.stock party good +
        (Physical.Public.interpreter source.native.input).totalCredit (Optimality.Programme.Epoch.inventory source n) party good := by
  have actual := Optimality.Programme.the_entire_programme_has_its_original_material_balance source.native.input
    (Evolving.Epoch.Source.originalState source.native) (Optimality.Programme.Epoch.programme source n) party good
  rw [Optimality.Programme.Epoch.the_compiled_history_is_the_literal_actual_epoch_physical_current,
    Optimality.Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory] at actual
  exact actual

theorem every_new_epoch_claim_remains_in_the_original_full_financial_matrix
    (instrument : Instrument) (debtor holder : Party) :
    (Evolving.Epoch.History.currentAt source n).raw.claims instrument debtor holder =
      source.raw.claims instrument debtor holder + Financial.inventoryClaims (Physical.Public.interpreter source.native.input)
        (Optimality.Programme.Epoch.inventory source n) (instrument,debtor,holder) := by
  have actual := every_programme_preserves_the_entire_original_claim_matrix source.native.input
    (Evolving.Epoch.Source.originalState source.native) (Optimality.Programme.Epoch.programme source n) instrument debtor holder
  rw [Optimality.Programme.Epoch.the_compiled_history_is_the_literal_actual_epoch_physical_current,
    Optimality.Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory] at actual
  exact actual

/-- The producer is in the original returned Report inventory, including
source-selected fees and repairs. No external supplement can hide there. -/
theorem every_actual_epoch_material_gain_has_an_original_accepted_credit
    (party : Party) (good : Good)
    (gain : source.raw.stock party good < (Evolving.Epoch.History.currentAt source n).raw.stock party good) :
    ∃ item ∈ Optimality.Programme.Epoch.inventory source n,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request ∧
      0 < flowAt ((Physical.Public.interpreter source.native.input).actualCredit item.before item.request) party good := by
  have programmeGain : (Evolving.Epoch.Source.originalState source.native).raw.stock party good <
      (Optimality.Programme.run source.native.input (Evolving.Epoch.Source.originalState source.native)
        (Optimality.Programme.Epoch.programme source n)).raw.stock party good := by
    rw [Optimality.Programme.Epoch.the_compiled_history_is_the_literal_actual_epoch_physical_current]
    exact gain
  have actual := every_real_resource_gain_has_an_original_credit_producer source.native.input
    (Evolving.Epoch.Source.originalState source.native) (Optimality.Programme.Epoch.programme source n) party good programmeGain
  rw [Optimality.Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory] at actual
  exact actual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape
