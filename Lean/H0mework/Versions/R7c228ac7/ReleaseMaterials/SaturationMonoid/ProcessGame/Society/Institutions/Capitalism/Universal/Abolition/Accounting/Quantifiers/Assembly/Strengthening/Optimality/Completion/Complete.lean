import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.Institutional
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.ActiveControl.Minimum
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Recognition.Family

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion

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

/-- The achieved funded-cut minimum and exact strategy accounting coexist
with a fully rooted counterexample to unconditional full-task attainment. -/
structure ClearingCostClaimsClosedAt : Prop extends Root.InstitutionalCostedCapitalRootAt seed claim where
  every_live_native_attainer :
    ∀ {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
      {reader : Macro.Raw.Reader input depth count} (source : Clearing.Position input depth count reader)
      (binding : Evolving.Epoch.Binding source.native)
      (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
        input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source)),
    type_of% (ActiveControl.the_actual_native_attainer_keeps_the_active_control_and_same_completed_root source binding resources)
  every_live_epoch_comparison :
    ∀ {input : ProgrammeSource.Input Party Good Port Technology Instrument} {depth count : Nat}
      {reader : Macro.Raw.Reader input depth count} (source : Clearing.Position input depth count reader)
      (binding : Evolving.Epoch.Binding source.native)
      (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions
        input depth count (Clearing.Deployment.history source) (Clearing.Deployment.before source)) policy n reading,
    type_of% (ActiveControl.the_attained_native_minimum_dominates_every_live_control_epoch_strategy
      source binding resources policy n reading)
  rooted_counterexample_family : ∀ n, Recognition.RootedCompleteAt n
  complete_cost_improver : ∀ code cleared,
    type_of% (Recognition.every_completed_candidate_has_a_strictly_cheaper_rooted_complete_continuation code cleared)
  no_free_full_cost_attainment :
    type_of% Recognition.no_completed_candidate_can_beat_all_source_generated_rooted_clearances

theorem the_original_capital_root_closes_the_actual_clearing_cost_and_delay_quantifiers :
    ClearingCostClaimsClosedAt seed claim where
  toInstitutionalCostedCapitalRootAt := Root.the_original_root_compares_every_actual_institutional_clearing_strategy seed claim
  every_live_native_attainer := ActiveControl.the_actual_native_attainer_keeps_the_active_control_and_same_completed_root
  every_live_epoch_comparison := ActiveControl.the_attained_native_minimum_dominates_every_live_control_epoch_strategy
  rooted_counterexample_family := Recognition.the_actual_complete_family_is_certified_on_its_original_roots
  complete_cost_improver := Recognition.every_completed_candidate_has_a_strictly_cheaper_rooted_complete_continuation
  no_free_full_cost_attainment := Recognition.no_completed_candidate_can_beat_all_source_generated_rooted_clearances

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion
