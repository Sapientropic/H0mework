import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Society

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable (sourceStart : Nat)

abbrev socialCount := Macro.Ingress.cut Installation.input 1 sourceStart

def socialLocalRead (past : List Installation.InputAt) : Installation.InputAt :=
  Observation.scheduledProposal Installation.input 1 (socialCount sourceStart) 0 0
    (Installation.sourceCut past) Installation.rule
    (Observation.programmeFromSensor Installation.rule Installation.programme) (Installation.publicPast past)

def socialReader (nature : Installation.RequestAt) : Macro.Raw.Reader Installation.input 1 (socialCount sourceStart) :=
  fun cursor _ => Installation.selectedWith (socialLocalRead sourceStart) nature cursor.past

def socialDatum : Macro.Ingress.Datum Installation.input 1 sourceStart where
  reader := fun _ => .primitive Control.Scenario.ownerPresent

abbrev socialCurrent (nature : Installation.RequestAt) (tick : Nat) :=
  Macro.Runtime.actualFrame (review := none) Installation.input 1 sourceStart (socialDatum sourceStart) 0 0
    (socialReader sourceStart nature) tick

theorem the_social_reader_uses_the_same_fixed_trial_code_and_local_paid_reader
    (nature : Installation.RequestAt) (cursor : Installation.CursorAt)
    (account : (Epoch.Finance.process Installation.input 1 (socialCount sourceStart)).GeneratedState) :
    socialReader sourceStart nature cursor account =
      Installation.selectedWith (socialLocalRead sourceStart) nature cursor.past := rfl

theorem every_social_funding_submission_precedes_the_unknown_event
    (first second : Installation.RequestAt) (past : List Installation.InputAt)
    (preparing : (Installation.publicPast past).length ≤ Installation.preparation.length) :
    Installation.selectedWith (socialLocalRead sourceStart) first past =
      Installation.selectedWith (socialLocalRead sourceStart) second past := by
  unfold Installation.selectedWith
  split
  · cases splitPast : Installation.publicPast past with
    | nil => rfl
    | cons baseline rest =>
        have bound : rest.length < Installation.preparation.length := by
          rw [splitPast, List.length_cons] at preparing
          omega
        simp only [if_pos bound]
  · rfl

theorem the_social_trial_reader_has_no_access_to_hidden_financial_state
    (nature : Installation.RequestAt) (cursor : Installation.CursorAt)
    (first second : (Epoch.Finance.process Installation.input 1 (socialCount sourceStart)).GeneratedState) :
    socialReader sourceStart nature cursor first = socialReader sourceStart nature cursor second := rfl

theorem originalCapitalRegistration : 0 < ProgrammeSource.registrationSize Installation.input :=
  Abolition.Completion.Actual.External.Admission.an_actual_source_capital_relation_generates_positive_registration
    Installation.input Control.Scenario.start Control.Scenario.originalCapital

theorem the_same_society_root_consumes_the_ex_ante_innovation_reader
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (nature : Installation.RequestAt) :
    Abolition.Completion.Actual.Assembly.SocietyCapitalLawAt Installation.input originalCapitalRegistration
      oldVisit sourceIndex boundary sourceStart (socialDatum sourceStart) 0 0 (socialReader sourceStart nature) none :=
  Abolition.Completion.Actual.Assembly.the_same_society_root_consumes_the_universal_capital_law
    Installation.input originalCapitalRegistration oldVisit sourceIndex boundary sourceStart
    (socialDatum sourceStart) 0 0 (socialReader sourceStart nature) none

theorem every_social_trial_attempt_keeps_the_original_claims_whole_ledger_and_generated_next
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (nature : Installation.RequestAt) (tick : Nat) :
    type_of% (Abolition.Completion.Actual.External.the_same_society_source_carries_every_actual_capital_update
      (review := none) Installation.input originalCapitalRegistration oldVisit sourceIndex boundary
      Installation.the_original_input_has_zero_genesis_claims_and_no_trial_future.1 sourceStart
      (socialDatum sourceStart) 0 0 (socialReader sourceStart nature) tick) :=
  Abolition.Completion.Actual.External.the_same_society_source_carries_every_actual_capital_update
    (review := none) Installation.input originalCapitalRegistration oldVisit sourceIndex boundary
    Installation.the_original_input_has_zero_genesis_claims_and_no_trial_future.1 sourceStart
    (socialDatum sourceStart) 0 0 (socialReader sourceStart nature) tick

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Completion
