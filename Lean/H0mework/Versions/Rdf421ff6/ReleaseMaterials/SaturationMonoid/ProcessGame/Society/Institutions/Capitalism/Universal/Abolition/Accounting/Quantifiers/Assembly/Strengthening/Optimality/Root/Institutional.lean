import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.EpochMinimum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

/-- Actual programme-law histories, including their real review fees,
consume the same original paid cut and complete capital contract. -/
structure InstitutionalCostedCapitalRootAt : Prop extends CostedCapitalRootAt seed claim where
  every_actual_epoch_competitor :
    ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
      (reader : Macro.Raw.Reader seed.input seed.depth seed.count)
      (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions seed.input seed.depth seed.count
        (Clearing.Deployment.history (Clearing.Deployment.Canonical.original seed claim enough reader)) (Clearing.Deployment.before (Clearing.Deployment.Canonical.original seed claim enough reader)))
      policy n reading,
    type_of% (the_achieved_native_minimum_dominates_every_actual_epoch_strategy
      (Clearing.Deployment.Canonical.original seed claim enough reader) resources policy n reading)
  actual_cost_history_is_not_deleted :
    ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
      (reader : Macro.Raw.Reader seed.input seed.depth seed.count) policy n reading,
    type_of% (the_minimum_preserves_all_incurred_costs_against_every_actual_epoch_strategy
      (Clearing.Deployment.Canonical.original seed claim enough reader) policy n reading)
  every_actual_epoch_has_its_literal_compiled_current : ∀ source n,
    type_of% (Programme.Epoch.the_compiled_history_is_the_literal_actual_epoch_physical_current
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) source n)
  every_actual_epoch_has_its_literal_report_inventory : ∀ source n,
    type_of% (Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory
      (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) source n)

theorem the_original_root_compares_every_actual_institutional_clearing_strategy :
    InstitutionalCostedCapitalRootAt seed claim where
  toCostedCapitalRootAt := the_original_root_consumes_actual_cost_minimisation_and_every_delay_comparison seed claim
  every_actual_epoch_competitor := fun enough reader =>
    the_achieved_native_minimum_dominates_every_actual_epoch_strategy (Clearing.Deployment.Canonical.original seed claim enough reader)
  actual_cost_history_is_not_deleted := fun enough reader =>
    the_minimum_preserves_all_incurred_costs_against_every_actual_epoch_strategy (Clearing.Deployment.Canonical.original seed claim enough reader)
  every_actual_epoch_has_its_literal_compiled_current :=
    Programme.Epoch.the_compiled_history_is_the_literal_actual_epoch_physical_current
  every_actual_epoch_has_its_literal_report_inventory :=
    Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root
