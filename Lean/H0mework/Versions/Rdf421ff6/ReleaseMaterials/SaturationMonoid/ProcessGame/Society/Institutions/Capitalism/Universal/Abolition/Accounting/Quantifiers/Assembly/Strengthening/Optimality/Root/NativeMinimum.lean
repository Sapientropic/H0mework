import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.PastCost
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native.Root

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
  (resources : Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
    input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source))

/-- The achieved minimum is a real root clearance. Needs of a different
unpaid task are not inferred from this native-account retirement. -/
structure RootedNativeCostMinimumAt : Prop where
  actual_whole_clearance : Clearing.Deployment.CompleteAt source resources
  exact_material_occurrence : type_of% (Cost.Canonical.the_costed_programme_is_the_same_completed_actual_root_physical_current
    source resources)
  all_original_financial_positions : ∀ (members : Party → Bool) good,
    Coalition.read members good (Delay.Native.actualNativeIncome source) = 0
  minimum_over_all_source_syntax : ∀ rival channel party good,
    type_of% (Cost.Canonical.no_alternative_programme_has_less_real_resource_or_time_cost source rival channel party good)
  every_fixed_readout_minimum : ∀ reading rival,
    type_of% (Cost.Canonical.every_fixed_nonnegative_readout_is_globally_minimal_over_all_source_programmes source reading rival)

theorem the_same_actual_root_attains_the_complete_native_retirement_minimum :
    RootedNativeCostMinimumAt source resources where
  actual_whole_clearance := (Delay.Native.the_actual_root_clears_all_original_debts_without_financial_timing_income source resources).1
  exact_material_occurrence := Cost.Canonical.the_costed_programme_is_the_same_completed_actual_root_physical_current source resources
  all_original_financial_positions :=
    (Delay.Native.the_actual_root_clears_all_original_debts_without_financial_timing_income source resources).2
  minimum_over_all_source_syntax := Cost.Canonical.no_alternative_programme_has_less_real_resource_or_time_cost source
  every_fixed_readout_minimum := Cost.Canonical.every_fixed_nonnegative_readout_is_globally_minimal_over_all_source_programmes source

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root
