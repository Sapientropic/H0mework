import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Registration
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program Source.ProgrammeControl
open Source.ProgrammeControl.Kernel.AssetAuthority
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (positive : 0 < ProgrammeSource.registrationSize input)
  (oldVisit : OldVisit) (sourceIndex boundary sourceStart : Nat)
  (datum : Macro.Ingress.Datum input 1 sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input 1 (Macro.Ingress.cut input 1 sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "decision" => External.ClaimsReceipt.actualDecision input positive oldVisit sourceIndex boundary
local notation "current" => Macro.Runtime.actualFrame (review := review)
  input 1 sourceStart datum prefixLimit renewalLimit reader

/-- The initial matrix is judged by the original actual ingress receipt.
A represented source enters the same mixed Engine and its full universal
contract. An unrepresented original debt remains an exact source residual;
it is never silently signed as a balanced native account. -/
def SocietyCapitalLawAt : Prop :=
  type_of% (External.the_programme_input_uses_the_existing_society_payment input oldVisit sourceIndex boundary) ∧
  type_of% (External.ClaimsReceipt.the_same_actual_runtime_consumes_the_original_input_and_financial_ingress
    input positive oldVisit sourceIndex boundary) ∧
  type_of% (External.ClaimsReceipt.the_actual_registered_input_is_the_same_complete_raw_source
    input oldVisit sourceIndex boundary) ∧
  match decision with
  | .represented matching =>
      let zero := matching.trans (External.Admission.the_canonical_native_genesis_has_zero_claims input)
      ∀ tick,
        type_of% (External.the_same_society_source_carries_every_actual_capital_update (review := review)
          input positive oldVisit sourceIndex boundary zero sourceStart datum prefixLimit renewalLimit reader tick) ∧
        CapitalTerminationAndFutureExpansionAt input 1 sourceStart datum prefixLimit renewalLimit reader review tick ∧
        ¬ LegallyAbsorbingActualCapitalControl input 1 sourceStart datum prefixLimit renewalLimit reader review tick ∧
        type_of% (Finite.the_actual_source_forces_a_finite_public_tail_or_its_exact_obstruction
          input 1 sourceStart datum prefixLimit renewalLimit reader review tick) ∧
        type_of% (every_legal_actual_path_reaches_complete_abolition_or_a_visible_residual
          input 1 sourceStart datum prefixLimit renewalLimit reader review tick) ∧
        (∀ members task,
          type_of% (every_function_in_the_actual_source_has_a_public_functional_replacement (current tick) members task)) ∧
        CompleteInitialSourceChoice (current tick) ∧
        ∀ (origin : Functions.Revision.Context (input := input) (review := review)
            1 (Macro.Ingress.cut input 1 sourceStart) prefixLimit renewalLimit 1 (Macro.Ingress.cut input 1 sourceStart))
            (admission : Functions.Revision.InitialAdmissionAt origin)
            (frame : Macro.Public.Runtime.Frame origin admission),
          ∀ selected : current tick = .enacted origin admission frame,
            CompletePublicDisposition frame ∧
            ∀ (complete : ¬ frame.HasWork) (automatic : Macro.Runtime.originalProposal frame = .advance),
              type_of% (every_available_complete_renewal_is_executed_with_its_actual_witness
                input 1 sourceStart datum prefixLimit renewalLimit reader review frame tick selected complete automatic)
  | .residual _issue =>
      (∃ instrument debtor creditor,
        input.initial.claims instrument debtor creditor ≠ External.Admission.nativeInitialClaims input instrument debtor creditor) ∧
      input.initial.claims ≠ External.Admission.nativeInitialClaims input ∧
      type_of% (External.ClaimsReceipt.the_actual_ingress_preserves_the_whole_generated_living_law
        input positive oldVisit sourceIndex boundary) ∧
      type_of% (External.ClaimsReceipt.the_actual_ingress_keeps_its_original_root_next
        input positive oldVisit sourceIndex boundary)

theorem the_same_society_root_consumes_the_universal_capital_law :
    SocietyCapitalLawAt input positive oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader review := by
  refine ⟨External.the_programme_input_uses_the_existing_society_payment input oldVisit sourceIndex boundary,
    External.ClaimsReceipt.the_same_actual_runtime_consumes_the_original_input_and_financial_ingress
      input positive oldVisit sourceIndex boundary,
    External.ClaimsReceipt.the_actual_registered_input_is_the_same_complete_raw_source input oldVisit sourceIndex boundary, ?_⟩
  cases generated : decision with
  | represented matching =>
      intro tick
      exact ⟨External.the_same_society_source_carries_every_actual_capital_update (review := review)
        input positive oldVisit sourceIndex boundary
        (matching.trans (External.Admission.the_canonical_native_genesis_has_zero_claims input))
        sourceStart datum prefixLimit renewalLimit reader tick,
        the_original_root_consumes_capital_termination_and_social_future_expansion
          input 1 sourceStart datum prefixLimit renewalLimit reader review tick,
        no_actual_source_form_can_obtain_a_legally_absorbing_capital_finality
          input 1 sourceStart datum prefixLimit renewalLimit reader review tick,
        Finite.the_actual_source_forces_a_finite_public_tail_or_its_exact_obstruction
          input 1 sourceStart datum prefixLimit renewalLimit reader review tick,
        every_legal_actual_path_reaches_complete_abolition_or_a_visible_residual
          input 1 sourceStart datum prefixLimit renewalLimit reader review tick,
        every_function_in_the_actual_source_has_a_public_functional_replacement (current tick),
        every_original_boundary_selects_an_available_complete_replacement (current tick),
        fun _origin _admission frame selected =>
          ⟨the_same_actual_public_source_generates_a_complete_witness_or_its_exact_residual frame,
            fun complete automatic => every_available_complete_renewal_is_executed_with_its_actual_witness
              input 1 sourceStart datum prefixLimit renewalLimit reader review frame tick selected complete automatic⟩⟩
  | residual issue =>
      exact ⟨issue.has_an_exact_original_matrix_coordinate input, issue.unrepresented,
        External.ClaimsReceipt.the_actual_ingress_preserves_the_whole_generated_living_law
          input positive oldVisit sourceIndex boundary,
        External.ClaimsReceipt.the_actual_ingress_keeps_its_original_root_next
          input positive oldVisit sourceIndex boundary⟩

variable {input}

/-- The C witness itself supplies positive source registration. Neither a
wage form, two-household carrier, fixed price, erased debt, nor a completed
future is a premise of this all-form source theorem. -/
theorem every_actual_source_capital_relation_has_the_original_society_termination_contract
    (capitalCurrent : RawCurrent Party Good Technology Instrument)
    (capital : Kernel.CapitalRelationKernel input.law capitalCurrent (ProgrammeSource.wordAt input capitalCurrent)) :
    ∃ registered : 0 < ProgrammeSource.registrationSize input,
      SocietyCapitalLawAt input registered oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader review :=
  ⟨External.Admission.an_actual_source_capital_relation_generates_positive_registration input capitalCurrent capital,
    the_same_society_root_consumes_the_universal_capital_law input
      (External.Admission.an_actual_source_capital_relation_generates_positive_registration input capitalCurrent capital)
      oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader review⟩

theorem every_original_control_form_has_the_same_society_termination_contract
    (visit : RootFace.Visit input)
    (use : ControlUse input.law (ProgrammeSource.rawCurrent input visit.current)
      (ProgrammeSource.rawEvent input visit.current) (Structural.familyAtVisit input visit)) :
    ∃ registered : 0 < ProgrammeSource.registrationSize input,
      SocietyCapitalLawAt input registered oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader review :=
  ⟨the_original_actual_instruction_generates_positive_registration input visit use.item,
    the_same_society_root_consumes_the_universal_capital_law input
      (the_original_actual_instruction_generates_positive_registration input visit use.item)
      oldVisit sourceIndex boundary sourceStart datum prefixLimit renewalLimit reader review⟩

#print axioms the_same_society_root_consumes_the_universal_capital_law
#print axioms every_actual_source_capital_relation_has_the_original_society_termination_contract
#print axioms every_original_control_form_has_the_same_society_termination_contract

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
