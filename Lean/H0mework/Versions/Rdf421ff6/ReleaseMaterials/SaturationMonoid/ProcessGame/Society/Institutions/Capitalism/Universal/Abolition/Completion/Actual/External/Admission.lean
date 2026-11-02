import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.ClaimsReceipt.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.InputOrigin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.Core

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Source.ProgrammeControl
open M14SourceGeneratedContributionMergeActionSource

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
/-- A generated C witness contains an original source instruction. Static
empty code cannot generate that witness; dynamic registration is already positive. -/
theorem an_actual_source_capital_relation_generates_positive_registration
    (current : RawCurrent Party Good Technology Instrument)
    (capital : Kernel.CapitalRelationKernel input.law current (ProgrammeSource.wordAt input current)) :
    0 < ProgrammeSource.registrationSize input := by
  cases emitted : input.emission? with
  | some emit => exact ProgrammeSource.generated_registration_positive input emit emitted
  | none =>
      rw [ProgrammeSource.registrationSize_fixed input emitted]
      apply List.length_pos_iff.mpr
      intro empty
      have original := capital.proposal.access.access.property
      simp only [ProgrammeSource.wordAt, emitted, empty, RawLaw.rawItems, RawLaw.execute,
        List.not_mem_nil] at original


variable (oldVisit : OldVisit) (sourceIndex boundary : Nat)

omit [DecidableEq Port] in
theorem an_empty_programme_keeps_the_original_legacy_route_and_full_raw_bearer
    (empty : ProgrammeSource.registrationSize input = 0) :
    InputSource.selectedInput (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary = none ∧
    InputSource.producedRevision (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary
      (Financial.Installation.Runtime.inputQuery input oldVisit sourceIndex boundary) =
        InputSource.legacyRevision (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary ∧
    (InputSource.registeredInput (Financial.Installation.Runtime.datum input)
      (InputSource.visit (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary)).query.raw =
        .programme input ∧
    type_of% (InputSource.original_row_and_successor_preserved
      (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary) := by
  have legacy : InputSource.selectedInput (Financial.Installation.Runtime.datum input)
      oldVisit sourceIndex boundary = none := by
    simp [InputSource.selectedInput, InputSource.chosenInput, InputSource.germAt,
      Financial.Installation.Runtime.datum, empty]
  refine ⟨legacy, ?_, rfl, InputSource.original_row_and_successor_preserved
    (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary⟩
  have selected := (InputSource.chosen_is_source_selected
    (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary
    (Financial.Installation.Runtime.inputQuery input oldVisit sourceIndex boundary)).trans legacy
  unfold InputSource.producedRevision
  erw [selected]

theorem an_unrepresented_initial_matrix_keeps_its_original_source_and_row
    (_issue : InitialClaimsResidual input) :
    (InputSource.registeredInput (Financial.Installation.Runtime.datum input)
      (InputSource.visit (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary)).query.raw =
        .programme input ∧
    type_of% (InputSource.original_row_and_successor_preserved
      (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary) :=
  ⟨rfl, InputSource.original_row_and_successor_preserved
    (Financial.Installation.Runtime.datum input) oldVisit sourceIndex boundary⟩

#print axioms an_actual_source_capital_relation_generates_positive_registration
#print axioms the_canonical_native_genesis_has_zero_claims
#print axioms inspectInitialClaims
#print axioms a_residual_cannot_be_signed_as_an_initial_native_balance
#print axioms the_source_genesis_condition_is_exact
#print axioms an_empty_programme_keeps_the_original_legacy_route_and_full_raw_bearer
#print axioms an_unrepresented_initial_matrix_keeps_its_original_source_and_row

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Admission
