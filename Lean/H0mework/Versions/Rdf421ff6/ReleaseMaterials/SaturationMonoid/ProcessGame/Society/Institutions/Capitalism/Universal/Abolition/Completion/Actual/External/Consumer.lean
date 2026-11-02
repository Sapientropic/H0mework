import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (positive : 0 < ProgrammeSource.registrationSize input)
  (oldVisit : OldVisit) (sourceIndex boundary : Nat)
  (initialZero : input.initial.claims = fun _ _ _ => 0)
  (sourceStart : Nat) (datum : Macro.Ingress.Datum input 1 sourceStart)
  (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input 1 (Macro.Ingress.cut input 1 sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

/-- The existing Society Payment source, its actual programme revision and
financial cut, and the original mixed-law Engine consume one continuous
source lineage. Every actual cut carries the complete external financial
Run, all original claims and history, and its own whole-ledger generated next.
The boundary is the already installed depth-one external genesis. -/
theorem the_same_society_source_carries_every_actual_capital_update (tick : Nat) :
    type_of% (the_programme_input_uses_the_existing_society_payment input oldVisit sourceIndex boundary) ∧
    type_of% (the_original_external_root_consumes_the_source_selected_programme
      input positive oldVisit sourceIndex boundary initialZero) ∧
    type_of% (the_macro_source_is_an_actual_external_payment_cut
      input positive oldVisit sourceIndex boundary initialZero sourceStart) ∧
    type_of% (the_registered_macro_input_keeps_that_exact_external_occurrence
      (review := review) input sourceStart datum prefixLimit renewalLimit) ∧
    type_of% (the_external_cut_generates_the_original_macro_action
      (review := review) input sourceStart datum prefixLimit renewalLimit reader) ∧
    type_of% (the_original_engine_consumes_the_external_source_action
      (review := review) input sourceStart datum prefixLimit renewalLimit reader) ∧
    Nonempty ((Epoch.Finance.process input 1 (Macro.Ingress.cut input 1 sourceStart)).Run
      (Epoch.Finance.Legacy.generated input 1 (Macro.Ingress.cut input 1 sourceStart)
        ((Macro.Ingress.frame input 1 sourceStart).cursor input).account).current
      (Macro.Runtime.actualFrame (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader tick).nativeAccount.current) ∧
    type_of% (every_original_external_claim_and_history_entry_survives
      (review := review) input sourceStart datum prefixLimit renewalLimit reader tick) ∧
    type_of% (every_actual_external_continuation_has_the_original_whole_ledger_next
      (review := review) input sourceStart datum prefixLimit renewalLimit reader tick) :=
  ⟨the_programme_input_uses_the_existing_society_payment input oldVisit sourceIndex boundary,
    the_original_external_root_consumes_the_source_selected_programme input positive oldVisit sourceIndex boundary initialZero,
    the_macro_source_is_an_actual_external_payment_cut input positive oldVisit sourceIndex boundary initialZero sourceStart,
    the_registered_macro_input_keeps_that_exact_external_occurrence (review := review)
      input sourceStart datum prefixLimit renewalLimit,
    the_external_cut_generates_the_original_macro_action (review := review)
      input sourceStart datum prefixLimit renewalLimit reader,
    the_original_engine_consumes_the_external_source_action (review := review)
      input sourceStart datum prefixLimit renewalLimit reader,
    ⟨nativeRun (review := review) input sourceStart datum prefixLimit renewalLimit reader tick⟩,
    every_original_external_claim_and_history_entry_survives (review := review)
      input sourceStart datum prefixLimit renewalLimit reader tick,
    every_actual_external_continuation_has_the_original_whole_ledger_next (review := review)
      input sourceStart datum prefixLimit renewalLimit reader tick⟩

#print axioms the_same_society_source_carries_every_actual_capital_update

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External
