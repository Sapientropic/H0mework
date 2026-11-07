import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.ActiveControl.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.AfterNative.Deployment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.ActiveControl
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader) (binding : Evolving.Epoch.Binding source.native)

variable (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
  input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))

theorem the_actual_native_attainer_keeps_the_active_control_and_same_completed_root :
    Root.RootedNativeCostMinimumAt source resources ∧
      (Evolving.Epoch.AfterNative.resume source binding resources).native = Clearing.Deployment.completed source resources ∧
      (Evolving.Epoch.AfterNative.resume source binding resources).control = binding.value ∧
      (Evolving.Epoch.AfterNative.resume source binding resources).inquiry.erase = (Clearing.Deployment.completed source resources).erase ∧
      Evolving.Epoch.Current.ClosedAt (Evolving.Epoch.AfterNative.resume source binding resources) :=
  ⟨Root.the_same_actual_root_attains_the_complete_native_retirement_minimum source resources,
    Evolving.Epoch.AfterNative.resume_is_the_literal_completed_native_current source binding resources,
    Evolving.Epoch.AfterNative.resume_reads_the_original_source_control source binding resources,
    Evolving.Epoch.AfterNative.resume_uses_the_same_completed_root_occurrence source binding resources,
    Evolving.Epoch.AfterNative.the_restored_epoch_programme_actually_reads_the_live_control_and_advances source binding resources⟩

theorem the_attained_native_minimum_dominates_every_live_control_epoch_strategy
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    (Root.RootedNativeCostMinimumAt source resources ∧
      (Evolving.Epoch.AfterNative.resume source binding resources).control = binding.value) ∧
    Cost.value reading input (Cost.Canonical.before source) (Cost.Canonical.programme source) ≤
      actualCost source binding policy n reading :=
  ⟨⟨Root.the_same_actual_root_attains_the_complete_native_retirement_minimum source resources,
      Evolving.Epoch.AfterNative.resume_reads_the_original_source_control source binding resources⟩,
    Cost.Canonical.every_fixed_nonnegative_readout_is_globally_minimal_over_all_source_programmes
      source reading (Programme.Epoch.programme (rival source binding policy) n)⟩

theorem the_minimum_with_active_control_keeps_all_already_incurred_source_costs
    (policy : Macro.Raw.Reader input depth count) (n : Nat) (reading : Cost.LinearReadout Party Good) :
    Root.fullHistoryCost source reading (Cost.Canonical.programme source) ≤
      Root.fullHistoryCost source reading (Programme.Epoch.programme (rival source binding policy) n) :=
  Root.the_actual_native_minimum_preserves_all_already_incurred_source_costs source reading _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.ActiveControl
