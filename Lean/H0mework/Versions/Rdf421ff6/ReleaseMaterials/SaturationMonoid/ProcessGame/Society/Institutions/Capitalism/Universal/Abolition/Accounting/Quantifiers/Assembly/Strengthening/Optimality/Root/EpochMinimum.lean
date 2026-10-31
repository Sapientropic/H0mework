import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.CommonPast
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Epoch.Readings
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Reader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader)

/-- An arbitrary observer-selected continuation of this exact original cut.
The original root supplies its physical state, control and complete account. -/
def challenger (policy : Macro.Raw.Reader input depth count) :=
  (Evolving.Epoch.Source.initial source.native).requery policy

theorem every_challenger_keeps_the_original_physical_cut (policy : Macro.Raw.Reader input depth count) :
    Evolving.Epoch.Source.originalState (challenger source policy).native = Cost.Canonical.before source := by
  change Public.Scope.actualState input depth count 0 0 [] source.actual.snapshot = _
  exact Clearing.Position.raw_state_is_read_from_its_actual_past source

theorem every_challenger_keeps_the_original_control_and_complete_account
    (policy : Macro.Raw.Reader input depth count) :
    (challenger source policy).control = (Evolving.Epoch.Source.initial source.native).control ∧
      (challenger source policy).native.actual.actual.account = source.actual.actual.account :=
  (Evolving.Epoch.Source.initial source.native).requery_keeps_control_and_complete_account policy

def actualEpochCost (policy : Macro.Raw.Reader input depth count) (n : Nat)
    (reading : Cost.LinearReadout Party Good) : ℚ :=
  Cost.value reading input (Cost.Canonical.before source) (Programme.Epoch.programme (challenger source policy) n)

/-- Fees are read from the actual returned reports. Native bookkeeping
does not replay a body or create a second material charge. -/
theorem the_competing_cost_is_the_actual_report_inventory_and_clock
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    actualEpochCost source policy n reading =
      ((Programme.Epoch.inventory (challenger source policy) n).map
        (Cost.itemValue reading (Physical.Public.interpreter input))).sum +
      reading.timeWeight * ((Evolving.Epoch.History.currentAt (challenger source policy) n).raw.clock -
        (challenger source policy).raw.clock) := by
  unfold actualEpochCost Cost.value
  rw [← every_challenger_keeps_the_original_physical_cut source policy]
  have ownInput : (challenger source policy).native.input = input := rfl
  have actualItems := Programme.Epoch.the_compiled_history_is_the_same_actual_report_inventory (challenger source policy) n
  have actualClock := Programme.Epoch.the_cost_clock_is_the_actual_epoch_clock_difference (challenger source policy) n
  rw [ownInput] at actualItems actualClock
  rw [actualItems,actualClock]

theorem the_achieved_native_minimum_dominates_every_actual_epoch_strategy
    (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
      input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    RootedNativeCostMinimumAt source resources ∧
      Cost.value reading input (Cost.Canonical.before source) (Cost.Canonical.programme source) ≤
        actualEpochCost source policy n reading :=
  ⟨the_same_actual_root_attains_the_complete_native_retirement_minimum source resources,
    Cost.Canonical.every_fixed_nonnegative_readout_is_globally_minimal_over_all_source_programmes
      source reading (Programme.Epoch.programme (challenger source policy) n)⟩

theorem the_actual_epoch_cost_includes_the_complete_original_past
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    fullHistoryCost source reading (Programme.Epoch.programme (challenger source policy) n) =
      Cost.value reading input (initialMaterial source) source.past + actualEpochCost source policy n reading :=
  the_actual_common_past_is_not_deleted_from_total_cost source reading _

theorem the_minimum_preserves_all_incurred_costs_against_every_actual_epoch_strategy
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    fullHistoryCost source reading (Cost.Canonical.programme source) ≤
      fullHistoryCost source reading (Programme.Epoch.programme (challenger source policy) n) :=
  the_actual_native_minimum_preserves_all_already_incurred_source_costs source reading _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root
