import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection.Verdict

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party) (proposal : RawEvent Party Good Port Technology Instrument)

private theorem actual_adjudication_retains_its_source
    (word : RawEvent Party Good Port Technology Instrument)
    (issue : Responsibility.Family.ObstructionAt claim state)
    (selected : Responsibility.Family.adjudicate claim state law word = .blocked issue) :
    issue.actualLaw = law ∧ issue.word = word := by
  unfold Responsibility.Family.adjudicate at selected
  cases inspected : Responsibility.Family.inspectPayment claim
      (Responsibility.Family.State.advance claim state law word)
      (Responsibility.Family.positiveScope source past nature response) with
  | paid complete => rw [inspected] at selected; cases selected
  | unpaid key member positive => rw [inspected] at selected; cases selected; exact ⟨rfl,rfl⟩

local notation "ev" => Policy.evaluate claim state law members proposal

theorem residual_is_the_same_actual_law_and_executed_word
    (issue : Responsibility.Family.ObstructionAt claim state)
    (noProgress : ¬ Progress.budget claim (ev).updated < Progress.budget claim state)
    (selected : renewalVerdict claim state law members proposal = .residual issue noProgress) :
    issue.actualLaw = law ∧ issue.word = (ev).executableWord := by
  unfold renewalVerdict at selected
  split at selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · cases selected
      · split at selected
        · cases selected
        · rename_i generated same
          have identical : generated = issue := by cases selected; rfl
          subst generated
          exact actual_adjudication_retains_its_source claim state law (ev).executableWord issue same
  · cases selected

theorem residual_exposes_a_positive_cell_in_the_actual_updated_row
    (issue : Responsibility.Family.ObstructionAt claim state)
    (noProgress : ¬ Progress.budget claim (ev).updated < Progress.budget claim state)
    (selected : renewalVerdict claim state law members proposal = .residual issue noProgress) :
    0 < (ev).updated.remaining issue.key := by
  obtain ⟨sameLaw,sameWord⟩ := residual_is_the_same_actual_law_and_executed_word claim state law members proposal
    issue noProgress selected
  have positive := issue.unpaid
  rw [sameLaw,sameWord] at positive
  exact positive

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Selection
