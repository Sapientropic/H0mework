import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Reading

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem every_original_resource_channel_reads_the_actual_epoch_inventory
    (n : Nat) (channel : Cost.Channel) (party : Party) (good : Good) :
    Cost.resource source.native.input (Evolving.Epoch.Source.originalState source.native)
        (programme source n) channel party good =
      ((inventory source n).map fun item => flowAt
        (Cost.actualPart (Physical.Public.interpreter source.native.input) item.before item.request channel) party good).sum := by
  rw [Cost.resource,the_compiled_history_is_the_same_actual_report_inventory]

theorem both_transfer_and_settlement_read_the_actual_same_inventory
    (n : Nat) (kind : Cost.Movement) (party : Party) (good : Good) :
    Cost.cashOut source.native.input (Evolving.Epoch.Source.originalState source.native)
        (programme source n) kind party good =
      ((inventory source n).map fun item => flowAt
        (Cost.movingDebit (Physical.Public.interpreter source.native.input) item kind) party good).sum ∧
    Cost.cashIn source.native.input (Evolving.Epoch.Source.originalState source.native)
        (programme source n) kind party good =
      ((inventory source n).map fun item => flowAt
        (Cost.movingCredit (Physical.Public.interpreter source.native.input) item kind) party good).sum := by
  simp only [Cost.cashOut,Cost.cashIn,the_compiled_history_is_the_same_actual_report_inventory,and_self]

theorem every_original_financial_address_has_the_actual_epoch_residual
    (n : Nat) (instrument : Instrument) (debtor holder : Party) :
    Cost.residualClaim source.native.input (Evolving.Epoch.Source.originalState source.native)
        (programme source n) instrument debtor holder =
      (Evolving.Epoch.History.currentAt source n).raw.claims instrument debtor holder := by
  rw [Cost.residualClaim,the_compiled_history_is_the_literal_actual_epoch_physical_current]
  rfl

theorem original_needs_and_maintenance_are_read_at_the_actual_epoch_target
    (n : Nat) (party : Party) :
    Cost.requiredNeeds source.native.input (Evolving.Epoch.Source.originalState source.native)
        (programme source n) party =
      (Physical.Public.interpreter source.native.input).necessities (Evolving.Epoch.History.currentAt source n).raw party ∧
    Cost.requiredMaintenance source.native.input (Evolving.Epoch.Source.originalState source.native)
        (programme source n) party =
      (Physical.Public.interpreter source.native.input).mandatoryMaintenance (Evolving.Epoch.History.currentAt source n).raw party := by
  simp only [Cost.requiredNeeds,Cost.requiredMaintenance,
    the_compiled_history_is_the_literal_actual_epoch_physical_current]
  exact ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch
