import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Offer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Compare
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Consumers.General
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Renewal.Decision
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.NoControl

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Completion

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : Trials.Mechanism Party Good Port Technology Instrument)

/-- The public programme is fixed before any raw event. Contributions,
failed attempts and later reactions keep their original signed source. -/
def SourceInnovationLawAt : Prop :=
  (∀ nature : source.Nature,
    type_of% ((Control.openedProgramme source).the_source_generated_trial_returns_the_complete_original_disposition nature)) ∧
  (∀ nature : source.Nature,
    ¬ Nonempty (Source.ProgrammeControl.Kernel.CapitalRelationKernel
      (Control.openedProgramme source).code.law source.code.initial ((Control.openedProgramme source).word nature))) ∧
  (∀ first second : source.Nature,
    type_of% ((Control.openedProgramme source).every_renewed_raw_attempt_generates_success_or_its_exact_original_failure
      first second)) ∧
  (∀ (first : source.Nature) (next : Trials.Mechanism Party Good Port Technology Instrument),
    type_of% ((Control.openedProgramme source).every_released_next_trial_has_paid_the_actual_first_period first next)) ∧
  ∀ (past : List (RawEvent Party Good Port Technology Instrument)) (nature : source.Nature)
    (response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (good : Good),
    type_of% (Control.every_unknown_event_and_finite_reaction_has_an_exact_cost_classification
      source past nature response good)

theorem every_committed_source_generates_open_innovation_or_its_exact_original_failure :
    SourceInnovationLawAt source := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro nature
    exact (Control.openedProgramme source).the_source_generated_trial_returns_the_complete_original_disposition nature
  · intro nature
    exact Functions.open_permissions_have_no_capital_kernel (physicalLaw source.code.law)
      (fun _ _ _ => rfl) _ _
  · intro first second
    exact (Control.openedProgramme source).every_renewed_raw_attempt_generates_success_or_its_exact_original_failure
      first second
  · intro first next
    exact (Control.openedProgramme source).every_released_next_trial_has_paid_the_actual_first_period first next
  · intro past nature response good
    exact Control.every_unknown_event_and_finite_reaction_has_an_exact_cost_classification source past nature response good

theorem the_public_mechanism_is_committed_before_every_possible_actual_event :
    (Control.openedProgramme source).code.initial = source.code.initial ∧
      (Control.openedProgramme source).funding = source.funding ∧
      (Control.openedProgramme source).investmentRequest = source.investmentRequest ∧
      (Control.openedProgramme source).closing = source.closing ∧
      HEq (Control.openedProgramme source).policy source.policy :=
  Control.the_two_runs_keep_one_source_seed_and_every_contribution_clause source

theorem the_source_quote_generates_participation_or_its_exact_issue
    (belief : source.QuotedNature → ℚ) (signal : Fin source.code.signals → Bool)
    (good : Good) (outside loading : ℚ) :
    match Contribution.makeOffer source belief signal good outside loading with
    | .offered _ =>
        Contribution.prefersParticipation (Contribution.forecastRows source belief signal good) outside loading = true ∧
          Contribution.expectedChange (Contribution.forecastRows source belief signal good)
            (Contribution.quotedReward source belief signal good outside loading) = outside + loading
    | .declined _ => ¬ Nonempty (Contribution.ProspectiveOffer source belief signal good outside loading) := by
  cases Contribution.makeOffer source belief signal good outside loading with
  | offered offer =>
      exact Contribution.every_offered_quote_generates_its_participation_choice source belief signal good outside loading offer
  | declined issue =>
      exact Contribution.an_exact_quote_issue_excludes_an_admitted_offer source belief signal good outside loading issue

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Completion
