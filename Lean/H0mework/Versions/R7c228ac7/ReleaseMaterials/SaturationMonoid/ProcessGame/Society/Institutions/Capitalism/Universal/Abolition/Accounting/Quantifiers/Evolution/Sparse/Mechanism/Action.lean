import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Mechanism.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Mechanism

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim)
  (programme : Programme claim) (input : Request Party Good Port Technology Instrument)

def next : Current (oldN := oldN) claim :=
  Sparse.nextCurrent claim (native claim current programme input) (word claim current programme input)

theorem next_reads_the_actual_updated_row :
    Current.state claim (next claim current programme input) =
      Responsibility.Family.State.advance claim (Current.state claim current) current.actualLaw
        (Gate.executableWord claim (native claim current programme input) (word claim current programme input)) := by
  unfold next
  rw [next_reads_the_actual_gated_state,source_state_is_the_same_original_row]
  rfl

theorem every_old_claim_is_preserved :
    (Current.state claim (next claim current programme input)).raw.claims = (Current.state claim current).raw.claims := by
  rw [next_reads_the_actual_updated_row]
  exact Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _

theorem no_original_cell_is_refilled (key : Party × Good) :
    (Current.state claim (next claim current programme input)).remaining key ≤ (Current.state claim current).remaining key := by
  rw [next_reads_the_actual_updated_row]
  exact Responsibility.Family.State.actual_advance_never_refills_any_original_cell _ _ _ _ _

theorem the_same_effective_law_and_roster_are_preserved :
    (next claim current programme input).actualLaw = current.actualLaw ∧
      (next claim current programme input).members = current.members := ⟨rfl,rfl⟩

theorem every_emitted_mechanism_is_an_actual_root_continuation :
    (RootInquiryCompletion.RootInquiryProcessNode.answered
      (Installation.presentation claim (native claim current programme input) (word claim current programme input)) PUnit.unit).erase =
      Current.erase claim (next claim current programme input) :=
  Installation.the_source_resumes_at_its_exact_updated_current _ _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Mechanism
