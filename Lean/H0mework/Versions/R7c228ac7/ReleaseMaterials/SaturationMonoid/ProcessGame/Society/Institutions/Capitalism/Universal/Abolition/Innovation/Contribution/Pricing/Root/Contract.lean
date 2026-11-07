import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Carrying
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Root.Contract

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
universe u v w x
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

structure SourceNativeRiskCompensationAt (source : C)
    (mechanism : Trials.Mechanism Party Good Port Technology Instrument) : Prop where
  originalLawAndCensus : type_of% (the_quote_reads_the_same_active_law_and_complete_actual_census source)
  originalCode : ∀ request, request ∈ source.control.remaining →
    request ∈ Material.Migration.sourceAlphabet (sourceInput source) source.raw
  generatedDisposition : PreparationDisposition source mechanism
  everyAttemptAccounted : ∀ nature proposed,
    Accounted source (attempt source mechanism nature proposed)
  sourceFailureNext : type_of% (the_failed_preparation_keeps_the_original_root_and_its_whole_ledger_next source)
  noInitialRefill : ∀ prepared : Prepared source mechanism,
    type_of% (the_proposed_initial_stock_cannot_refill_the_original_quote source mechanism prepared)
  witnessedOutside : ∀ prepared : Prepared source mechanism,
    type_of% (preparation_has_no_unwitnessed_outside_or_loading_parameter source mechanism prepared)
  allRiskBranches : ∀ (prepared : Prepared source mechanism) (signal : Fin mechanism.code.signals)
    (plan : Source.Quote (prepared.schedule.rows signal)),
    type_of% (Source.a_generated_price_preserves_every_matching_original_risk_branch prepared.schedule signal plan)
  leastNecessaryPayment : ∀ (prepared : Prepared source mechanism) (signal : Fin mechanism.code.signals)
    (plan : Source.Quote (prepared.schedule.rows signal)) other safe,
    type_of% (Source.a_generated_price_is_least_among_all_rules_using_that_local_information
      prepared.schedule signal plan other safe)
  exactRiskWrites : ∀ (prepared : Prepared source mechanism) nature proposed decision amount written,
    type_of% (Source.every_written_risk_claim_uses_exactly_the_generated_compensation
      prepared.schedule nature proposed decision amount written)
  noUnbackedRiskWrites : ∀ (prepared : Prepared source mechanism) nature proposed refused,
    type_of% (every_refused_risk_amount_sends_no_financial_requests prepared nature proposed refused)
  actualDelivery : ∀ (prepared : Prepared source mechanism) (nature : prepared.schedule.programme.QuotedNature) ready review,
    type_of% (the_prepared_default_payment_generates_its_same_whole_ledger_successor prepared nature ready review)
  actualFullEndpoint : ∀ (prepared : Prepared source mechanism) nature {afterBody target : C}
    (actualBody : Runtime.Trace source (bodyWord prepared nature) afterBody)
    (actualPrice : Runtime.Trace afterBody (priceWord prepared nature none) target),
    type_of% (the_returned_root_is_the_literal_complete_price_execution prepared nature actualBody actualPrice)
  wholeLedger : ∀ (prepared : Prepared source mechanism) nature {afterBody target : C}
    (actualBody : Runtime.Trace source (bodyWord prepared nature) afterBody)
    (actualPrice : Runtime.Trace afterBody (priceWord prepared nature none) target),
    type_of% (both_actual_phases_carry_every_original_row_without_refilling prepared nature actualBody actualPrice)
  standingPaid : ∀ (prepared : Prepared source mechanism) (nature : prepared.schedule.programme.QuotedNature) person present,
    type_of% (actual_risk_completion_keeps_each_original_living_and_maintenance_payment prepared nature person present)
  allBearerAccounts : ∀ (prepared : Prepared source mechanism) (nature : prepared.schedule.programme.QuotedNature) person good,
    type_of% (all_original_full_accounts_retain_both_real_outside_benchmarks prepared nature person good)

theorem the_actual_root_closes_source_generated_risk_compensation
    (source : C) (mechanism : Trials.Mechanism Party Good Port Technology Instrument) :
    SourceNativeRiskCompensationAt source mechanism where
  originalLawAndCensus := the_quote_reads_the_same_active_law_and_complete_actual_census source
  originalCode := the_actual_remaining_programme_is_in_the_quote_catalogue source
  generatedDisposition := every_actual_preparation_generates_its_price_execution_or_exact_source_obstruction source mechanism
  everyAttemptAccounted := every_actual_risk_attempt_carries_all_original_rows_and_claims source mechanism
  sourceFailureNext := the_failed_preparation_keeps_the_original_root_and_its_whole_ledger_next source
  noInitialRefill := the_proposed_initial_stock_cannot_refill_the_original_quote source mechanism
  witnessedOutside := preparation_has_no_unwitnessed_outside_or_loading_parameter source mechanism
  allRiskBranches := fun prepared => Source.a_generated_price_preserves_every_matching_original_risk_branch prepared.schedule
  leastNecessaryPayment := fun prepared => Source.a_generated_price_is_least_among_all_rules_using_that_local_information prepared.schedule
  exactRiskWrites := fun prepared => Source.every_written_risk_claim_uses_exactly_the_generated_compensation prepared.schedule
  noUnbackedRiskWrites := every_refused_risk_amount_sends_no_financial_requests
  actualDelivery := the_prepared_default_payment_generates_its_same_whole_ledger_successor
  actualFullEndpoint := the_returned_root_is_the_literal_complete_price_execution
  wholeLedger := both_actual_phases_carry_every_original_row_without_refilling
  standingPaid := actual_risk_completion_keeps_each_original_living_and_maintenance_payment
  allBearerAccounts := all_original_full_accounts_retain_both_real_outside_benchmarks

variable {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Abolition.Accounting.Quantifiers.Global.Seed (mechanism := mechanism)
    (past := past) (nature := nature) (response := response))
  (claim : Abolition.Accounting.Quantifiers.Entitlement.Source.Claim (Abolition.Accounting.Quantifiers.Joint.window seed))

structure CapitalRiskCompensationClosedAt : Prop extends Characterization.Root.MinimalSupportAndEscapeAt.{u,v,w,x} seed claim where
  everyActualRiskSource : ∀ source : C, ∀ proposal : Trials.Mechanism Party Good Port Technology Instrument,
    SourceNativeRiskCompensationAt source proposal

theorem the_original_capital_root_closes_the_risk_compensation_amount_and_authority :
    CapitalRiskCompensationClosedAt.{u,v,w,x} seed claim where
  toMinimalSupportAndEscapeAt := Characterization.Root.the_original_root_characterizes_minimal_support_and_every_legal_escape seed claim
  everyActualRiskSource := the_actual_root_closes_source_generated_risk_compensation

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
