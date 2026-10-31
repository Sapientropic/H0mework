import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Guarantee
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

/-- This quantifies over every finite primitive programme, including mixed
plants and revisions. Resources are raw source inequalities and guards;
neither a successful execution nor its endpoint is a premise. -/
theorem every_resource_sufficient_original_programme_actually_settles_the_same_root
    (declared : (Abolition.Accounting.Root.Reentry.Frame.state claim frame).declared = true)
    (resources : Adequacy.Capacity.Resources claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal) :
    Refusal.RefusalInstalledAt claim frame proposal ∧
      Root.Gate.executableWord claim frame proposal = proposal ∧
      Exit.Necessity.AllNeedsPaid frame.actualLaw
        (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw frame.members proposal ∧
      Responsibility.Family.State.isPaid claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim (Refusal.Action.nextFrame claim frame proposal)) := by
  have success := Adequacy.Capacity.sufficient_source_resources_generate_actual_success claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members proposal declared resources
  have complete := (Root.Gate.executableWord_eq_original_evaluation claim frame proposal).trans success.complete
  have actualWord := Policy.evaluation_actual_word_is_the_original_executable_word claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members
    (Policy.evaluate claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal)
  have needs := success.needs
  rw [actualWord,success.complete] at needs
  have paid := success.paid
  change Responsibility.Family.State.isPaid claim (Responsibility.Family.State.advance claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw
    (Policy.evaluate claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal).executableWord) at paid
  rw [success.complete] at paid
  refine ⟨Refusal.the_original_root_returns_refusal_liability_and_no_capital_renewal_authority claim frame proposal,
    complete,needs,?_⟩
  rw [Refusal.the_liability_is_read_on_the_same_actual_next_row,complete]
  exact paid

theorem sufficient_primitive_resources_force_actual_admission_on_an_unpaid_original_row
    (declared : (Abolition.Accounting.Root.Reentry.Frame.state claim frame).declared = true)
    (unpaid : ¬ Responsibility.Family.State.isPaid claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame))
    (resources : Adequacy.Capacity.Resources claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members proposal) : Root.Admitted claim frame proposal := by
  obtain ⟨permit,_selected⟩ := Adequacy.Capacity.source_resources_generate_a_selected_actual_admission claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members proposal declared unpaid resources
  exact an_actual_current_source_permit_cannot_be_ignored claim proposal frame permit

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness
