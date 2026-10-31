import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Exact
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Support.Consumers
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Claim
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Permissions.Return
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction.Surplus
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Models.Reconstruction.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Complete
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Escape.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program Source.ProgrammeControl Innovation
open Source.ProgrammeControl.Kernel.AssetAuthority
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.UniversalRootGrammar
open Abolition.Root Abolition.Root.Registered Evolution.Ingress.Joint Evolution.Ingress.Joint.Material
universe u v w x
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

structure MinimalSupportAndEscapeAt : Prop extends Optimality.Completion.ClearingCostClaimsClosedAt seed claim where
  minimalLawSupport : ∀ law : RawLaw Party Good Port Technology Instrument,
    Global.NoCapital law ↔ Support.NoAsymmetry law
  everyKernelFailure : ∀ (law : RawLaw Party Good Port Technology Instrument) raw word capital,
    type_of% (Support.every_kernel_exposes_its_actual_bearing_failure law raw word capital)
  everyTitleFailure : ∀ (law : RawLaw Party Good Port Technology Instrument) raw word capital,
    type_of% (Support.a_proper_title_retains_the_same_original_bearing_failure law raw word capital)
  everySurplusFailure : ∀ (law : RawLaw Party Good Port Technology Instrument) raw word capital,
    type_of% (Support.every_actual_surplus_retains_its_dependency_and_original_appropriation law raw word capital)
  everyReproductionFailure : ∀ (law : RawLaw Party Good Port Technology Instrument) raw word capital,
    type_of% (Support.every_contribution_reproduction_retains_its_original_private_production law raw word capital)
  everyHistoricalFailure : ∀ (input : ProgrammeSource.Input Party Good Port Technology Instrument) endpoint capital,
    type_of% (Support.every_historical_capital_exposes_its_original_and_current_bearing_failure input endpoint capital)
  exactOriginalFamily : ∀ (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (visit : RootFace.Visit input) (item : RootFace.Item input visit) port,
    type_of% (Support.original_source_failure_iff_unified_family_membership input visit item port)
  exactActualControlUse : ∀ (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (visit : RootFace.Visit input) (item : RootFace.Item input visit) port,
    type_of% (Support.actual_control_use_exists_iff_its_original_execution_checks input visit item port)
  everyKernelReconstructs : ∀ (law : RawLaw Party Good Port Technology Instrument) raw word proposal,
    type_of% (Models.Reconstruction.every_raw_source_reconstruction_generates_capital_or_an_exact_failed_guard law raw word proposal)
  everyAppropriationMode : ∀ (law : RawLaw Party Good Port Technology Instrument) raw word proposal evidence,
    type_of% (Models.Reconstruction.every_raw_appropriation_mode_has_an_exact_original_compiler_disposition law raw word proposal evidence)
  everyHistoricalMode : ∀ (input : ProgrammeSource.Input Party Good Port Technology Instrument) endpoint access reciprocal disposal evidence,
    type_of% (Models.Reconstruction.every_historical_mode_is_compiled_or_retains_an_exact_failed_source_guard
      input endpoint access reciprocal disposal evidence)
  actualCountermodels : ∀ owner recipient clock round,
    type_of% (Models.Permissions.capital_regeneration_is_exactly_the_two_actual_permission_atoms owner recipient clock round)
  actualClaimMode : ∀ clock round,
    type_of% (Models.Permissions.Claim.actual_original_issue_restores_the_claim_supported_relation clock round)
  actualSurplusMode : ∀ clock round,
    type_of% (Models.Permissions.Return.actual_appropriation_is_source_generated_at_every_clock clock round)
  allActualRoutes : ∀ source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument), Escape.AccountedActualHistoryAt source
  everyLawfulSubmission :
    ∀ {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}} {root : SourceNativeLivingRootClosure N V}
      {recognition : SourceNativeDependentFaceFamilyRecognitionAt root}
      {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
      {scenario : recognition.law.vocabulary.Scenario}
      {Visible : Type v} {Output : Type w} {ClaimedEffect : Type x}
      {attempt : SourceNativeObserverConsumerAttemptAt recognition visit scenario Visible Output ClaimedEffect}
      {submission : SourceNativeObserverConsumerSubmissionProgramAt attempt}
      (program : SourceNativeObserverConsumerLegislationProgramAt submission),
    SourceNativeRootLawCompleteAt program.generate ∧ SourceNativeU8AvailableAt program.generate

theorem the_original_root_characterizes_minimal_support_and_every_legal_escape :
    MinimalSupportAndEscapeAt.{u,v,w,x} seed claim where
  toClearingCostClaimsClosedAt := Optimality.Completion.the_original_capital_root_closes_the_actual_clearing_cost_and_delay_quantifiers seed claim
  minimalLawSupport := Support.the_existing_no_capital_contract_iff_its_minimal_permission_support
  everyKernelFailure := Support.every_kernel_exposes_its_actual_bearing_failure
  everyTitleFailure := Support.a_proper_title_retains_the_same_original_bearing_failure
  everySurplusFailure := Support.every_actual_surplus_retains_its_dependency_and_original_appropriation
  everyReproductionFailure := Support.every_contribution_reproduction_retains_its_original_private_production
  everyHistoricalFailure := Support.every_historical_capital_exposes_its_original_and_current_bearing_failure
  exactOriginalFamily := Support.original_source_failure_iff_unified_family_membership
  exactActualControlUse := Support.actual_control_use_exists_iff_its_original_execution_checks
  everyKernelReconstructs := Models.Reconstruction.every_raw_source_reconstruction_generates_capital_or_an_exact_failed_guard
  everyAppropriationMode := Models.Reconstruction.every_raw_appropriation_mode_has_an_exact_original_compiler_disposition
  everyHistoricalMode := Models.Reconstruction.every_historical_mode_is_compiled_or_retains_an_exact_failed_source_guard
  actualCountermodels := Models.Permissions.capital_regeneration_is_exactly_the_two_actual_permission_atoms
  actualClaimMode := Models.Permissions.Claim.actual_original_issue_restores_the_claim_supported_relation
  actualSurplusMode := Models.Permissions.Return.actual_appropriation_is_source_generated_at_every_clock
  allActualRoutes := Escape.every_actual_source_route_has_its_complete_original_account
  everyLawfulSubmission := Escape.every_lawful_source_program_has_whole_ledger_disposition_and_conditional_u8

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Characterization.Root
