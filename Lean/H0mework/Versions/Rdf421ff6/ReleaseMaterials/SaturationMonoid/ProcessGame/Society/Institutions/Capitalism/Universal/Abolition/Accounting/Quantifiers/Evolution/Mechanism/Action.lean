import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Mechanism.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Mechanism

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (frame : Root.Reentry.Frame (oldN := oldN) claim)
  (programme : Programme claim) (input : Request Party Good Port Technology Instrument)

def action := Priority.Refusal.Action.generated claim (native claim frame programme input) (word claim frame programme input)

def nextFrame : Root.Reentry.Frame (oldN := oldN) claim :=
  Priority.Refusal.Action.nextFrame claim (native claim frame programme input) (word claim frame programme input)

def reply := (action claim frame programme input).target.answer

theorem the_new_mechanism_is_executed_by_the_same_root_whole_ledger :
    Priority.Refusal.RefusalInstalledAt claim (native claim frame programme input) (word claim frame programme input) :=
  Priority.Refusal.the_original_root_returns_refusal_liability_and_no_capital_renewal_authority _ _ _

theorem the_original_row_reads_the_real_new_mechanism_effect :
    Root.Reentry.Frame.state claim (nextFrame claim frame programme input) =
      Responsibility.Family.State.advance claim (Root.Reentry.Frame.state claim frame) frame.actualLaw
        (Priority.Root.Gate.executableWord claim (native claim frame programme input) (word claim frame programme input)) := by
  unfold nextFrame
  rw [Priority.Refusal.the_liability_is_read_on_the_same_actual_next_row,source_state_is_the_same_original_row]
  rfl

theorem a_new_mechanism_preserves_every_original_financial_address :
    (Root.Reentry.Frame.state claim (nextFrame claim frame programme input)).raw.claims =
      (Root.Reentry.Frame.state claim frame).raw.claims := by
  rw [the_original_row_reads_the_real_new_mechanism_effect]
  exact Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _

theorem a_new_mechanism_cannot_refill_any_old_harm_cell (key : Party × Good) :
    (Root.Reentry.Frame.state claim (nextFrame claim frame programme input)).remaining key ≤
      (Root.Reentry.Frame.state claim frame).remaining key := by
  rw [the_original_row_reads_the_real_new_mechanism_effect]
  exact Responsibility.Family.State.actual_advance_never_refills_any_original_cell _ _ _ _ _

private theorem refusal_context_is_literal
    (source : Root.Reentry.Frame (oldN := oldN) claim)
    (proposal : RawEvent Party Good Port Technology Instrument) :
    (Priority.Refusal.Action.nextFrame claim source proposal).actualLaw = source.actualLaw ∧
      (Priority.Refusal.Action.nextFrame claim source proposal).members = source.members := ⟨rfl,rfl⟩

theorem actual_step_retains_the_original_law_roster_and_declared_phase :
    (nextFrame claim frame programme input).actualLaw = frame.actualLaw ∧
      (nextFrame claim frame programme input).members = frame.members ∧
      (Root.Reentry.Frame.state claim (nextFrame claim frame programme input)).declared =
        (Root.Reentry.Frame.state claim frame).declared := by
  have context := refusal_context_is_literal claim (native claim frame programme input) (word claim frame programme input)
  refine ⟨context.1,context.2,?_⟩
  rw [the_original_row_reads_the_real_new_mechanism_effect]
  rfl

theorem the_old_paid_row_is_not_revived_by_a_new_mechanism
    (paid : Responsibility.Family.State.isPaid claim (Root.Reentry.Frame.state claim frame)) :
    Responsibility.Family.State.isPaid claim (Root.Reentry.Frame.state claim (nextFrame claim frame programme input)) := by
  intro key original
  exact le_antisymm (by simpa only [paid key original] using
    a_new_mechanism_cannot_refill_any_old_harm_cell claim frame programme input key)
    ((Root.Reentry.Frame.state claim (nextFrame claim frame programme input)).nonnegative key)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Mechanism
