import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root.FundedPrefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native.Adaptive
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Trace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Complete

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

/-- The original root consumes the costed clearance and arbitrary-strategy
comparison. No minimum over unpaid alternative production tasks is assumed. -/
structure CostedCapitalRootAt : Prop extends Total.CapitalLineStrengthenedAt seed claim where
  every_funded_actual_cut : ∀ (enough : Quantifiers.Joint.Planning.Enough seed claim (shared seed claim))
    (reader : Macro.Raw.Reader seed.input seed.depth seed.count)
    (resources : Runtime.Retirement.CompleteLedger.ArchiveNative.Conditions seed.input seed.depth seed.count
      (Clearing.Deployment.history (Clearing.Deployment.Canonical.original seed claim enough reader))
      (Clearing.Deployment.before (Clearing.Deployment.Canonical.original seed claim enough reader))),
    FundedOriginalTaskAt seed claim enough reader resources
  every_adaptive_comparison : ∀ opening delayed baseline delayTicks baseTicks members good,
    type_of% (Delay.every_adaptive_pair_preserves_the_entire_coalition_comparison
      seed claim opening delayed baseline delayTicks baseTicks members good)
  original_matrices_never_refill : ∀ current proposals,
    type_of% (Delay.every_program_retains_both_original_residual_matrices seed claim current proposals)
  every_original_claim_follows_its_actual_effect : ∀ current proposals instrument debtor creditor,
    type_of% (Delay.every_original_financial_position_follows_its_actual_effect
      seed claim current proposals instrument debtor creditor)
  every_pure_retirement_strategy : ∀ opening policy
    (retirement : ∀ history current request, request ∈ policy history current → Delay.Native.RetirementRequest request)
    ticks members good,
    type_of% (Delay.Native.an_arbitrary_adaptive_retirement_strategy_cannot_gain_at_any_unpaid_prefix
      seed claim opening policy retirement ticks members good)

theorem the_original_root_consumes_actual_cost_minimisation_and_every_delay_comparison :
    CostedCapitalRootAt seed claim where
  toCapitalLineStrengthenedAt := Total.the_original_root_closes_the_full_strengthened_capital_quantifiers seed claim
  every_funded_actual_cut := the_real_paid_prefix_and_original_native_minimum_complete_one_source_task seed claim
  every_adaptive_comparison := Delay.every_adaptive_pair_preserves_the_entire_coalition_comparison seed claim
  original_matrices_never_refill := Delay.every_program_retains_both_original_residual_matrices seed claim
  every_original_claim_follows_its_actual_effect := Delay.every_original_financial_position_follows_its_actual_effect seed claim
  every_pure_retirement_strategy :=
    Delay.Native.an_arbitrary_adaptive_retirement_strategy_cannot_gain_at_any_unpaid_prefix seed claim

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Root
