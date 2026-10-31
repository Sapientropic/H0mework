import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.LinearSettlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
  {reader : Macro.Raw.Reader input depth count}
  (source : Clearing.Position input depth count reader) (reading : LinearReadout Party Good)

theorem the_actual_source_plan_attains_every_fixed_nonnegative_readout_zero :
    value reading input (before source) (programme source) = 0 :=
  every_fixed_nonnegative_readout_has_the_same_zero_extra_settlement_value reading input (before source)
    (Clearing.Deployment.plan source) (every_chosen_operation_comes_from_the_original_settlement_ledger source)

theorem every_fixed_nonnegative_readout_is_globally_minimal_over_all_source_programmes
    (rival : Programme.Submission (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    value reading input (before source) (programme source) ≤ value reading input (before source) rival := by
  rw [the_actual_source_plan_attains_every_fixed_nonnegative_readout_zero]
  exact value_nonnegative reading input (before source) rival

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Cost.Canonical
