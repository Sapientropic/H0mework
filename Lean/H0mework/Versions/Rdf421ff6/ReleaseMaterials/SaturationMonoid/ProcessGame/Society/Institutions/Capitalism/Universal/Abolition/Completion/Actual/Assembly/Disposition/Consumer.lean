import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly.Disposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Functions.Revision.InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission)

theorem the_generated_disposition_contains_real_migration_future_and_full_gain_or_an_exact_residual :
    match abolitionDisposition frame with
    | .abolished witness =>
        frame.snapshotRead.fullAccount = .accepted witness.financial ∧
        MigrationChecks origin admission ∧
        Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit origin.germ.snapshot.past
          frame.snapshot (Functions.Revision.Adaptive.executable witness.future.rawWord) ∧
        (∀ person good, 0 ≤ Dividend.Financial.delta input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot person good) ∧
        ∃ person good, 0 < Dividend.Financial.delta input depth count prefixLimit renewalLimit
          origin.germ.snapshot.past frame.snapshot person good
    | .residual _ => ¬ Nonempty (AbolitionWitness frame) := by
  cases abolitionDisposition frame with
  | abolished witness =>
      exact ⟨witness.the_installed_read_is_the_literal_root_snapshot frame, witness.migration,
        witness.the_future_checks_every_current_standing frame,
        witness.the_full_account_has_no_loser_and_has_strict_gain frame⟩
  | residual failure => exact failure.excludes_a_success_witness frame

/-- This is a completeness consumer of the actual three inspectors. It
supplies raw current source syntax, not an abolition endpoint or future table. -/
theorem the_actual_three_checks_cannot_be_hidden_in_a_residual
    (financial : Dividend.Financial.Checks input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot)
    (migration : MigrationChecks origin admission)
    (word : RawEvent Party Good Port Technology Instrument)
    (generated : word ∈ Functions.Revision.Adaptive.candidates input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot)
    (checked : Functions.Revision.Adaptive.Checks input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot word) :
    ∃ witness, abolitionDisposition frame = .abolished witness := by
  cases selected : abolitionDisposition frame with
  | abolished witness => exact ⟨witness, rfl⟩
  | residual failure =>
      cases failure with
      | financial issue _ => exact False.elim (issue.refutes _ _ _ _ _ _ _ financial)
      | migration _ _ issue _ => exact False.elim (issue.refutes _ _ _ _ migration)
      | future _ _ _ _ obstruction _ => exact False.elim (obstruction.excluded word generated checked)

theorem an_original_financial_issue_is_returned_without_trying_to_fake_abolition
    (issue : Dividend.Financial.Issue input depth count prefixLimit renewalLimit
      origin.germ.snapshot.past frame.snapshot)
    (read : Dividend.Root.installedAssessment frame = .rejected issue) :
    abolitionDisposition frame = .residual (.financial issue read) := by
  unfold abolitionDisposition
  split
  · rename_i original generated
    have same : original = issue := Dividend.Financial.Decision.rejected.inj (generated.symm.trans read)
    cases same
    rfl
  · rename_i financial generated
    cases generated.symm.trans read

#print axioms the_generated_disposition_contains_real_migration_future_and_full_gain_or_an_exact_residual
#print axioms the_actual_three_checks_cannot_be_hidden_in_a_residual
#print axioms an_original_financial_issue_is_returned_without_trying_to_fake_abolition

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Assembly
