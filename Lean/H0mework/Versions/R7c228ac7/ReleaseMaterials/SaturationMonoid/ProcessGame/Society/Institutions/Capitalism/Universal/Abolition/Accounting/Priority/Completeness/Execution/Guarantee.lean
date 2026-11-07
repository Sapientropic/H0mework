import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution.Forced
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Universal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open Innovation

noncomputable section

attribute [local irreducible] Adequacy.Compiler.compile Adequacy.Compiler.word

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)

private theorem selected_resources_are_generated_on_the_same_source
    (enough : Adequacy.Compiler.Enough claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members) :
    Adequacy.Capacity.Resources claim (Abolition.Accounting.Root.Reentry.Frame.state claim (Source.native claim frame))
      (Source.native claim frame).actualLaw (Source.native claim frame).members (Source.word claim frame) := by
  obtain ⟨plan,selected⟩ := Adequacy.Compiler.enough_source_resources_force_a_generated_plan claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members enough
  change Adequacy.Capacity.Resources claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim (Source.native claim frame))
    frame.actualLaw frame.members (Source.word claim frame)
  rw [Source.state_eq,Source.word_eq,
    Adequacy.Compiler.the_compiled_word_is_exactly_the_source_selected_plan claim
      (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members plan selected]
  exact plan.resources

/-- The mechanism is fixed, then the current supplies its own resources.
When its source recipe condition holds, the selected plan is actually run. -/
theorem sufficient_current_resources_force_actual_whole_ledger_payment
    (declared : (Abolition.Accounting.Root.Reentry.Frame.state claim frame).declared = true)
    (enough : Adequacy.Compiler.Enough claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members) :
    Refusal.RefusalInstalledAt claim (Source.native claim frame) (Source.word claim frame) ∧
      Root.Gate.executableWord claim (Source.native claim frame) (Source.word claim frame) = Source.word claim frame ∧
      Exit.Necessity.AllNeedsPaid frame.actualLaw (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw
        frame.members (Source.word claim frame) ∧
      Responsibility.Family.State.isPaid claim (Abolition.Accounting.Root.Reentry.Frame.state claim (nextFrame claim frame)) := by
  have currentDeclared : (Abolition.Accounting.Root.Reentry.Frame.state claim (Source.native claim frame)).declared = true := by
    rw [Source.state_eq]
    exact declared
  have actual := every_resource_sufficient_original_programme_actually_settles_the_same_root claim
    (Source.native claim frame) (Source.word claim frame) currentDeclared
    (selected_resources_are_generated_on_the_same_source claim frame enough)
  refine ⟨actual.1,actual.2.1,?_,actual.2.2.2⟩
  have paidNeeds := actual.2.2.1
  change Exit.Necessity.AllNeedsPaid frame.actualLaw
    (Abolition.Accounting.Root.Reentry.Frame.state claim (Source.native claim frame)).raw
    frame.members (Source.word claim frame) at paidNeeds
  rwa [Source.state_eq] at paidNeeds

theorem sufficient_current_resources_force_actual_renewal_without_an_adoption_choice
    (declared : (Abolition.Accounting.Root.Reentry.Frame.state claim frame).declared = true)
    (unpaid : ¬ Responsibility.Family.State.isPaid claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame))
    (enough : Adequacy.Compiler.Enough claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members) :
    Root.Admitted claim (Source.native claim frame) (Source.word claim frame) := by
  apply sufficient_primitive_resources_force_actual_admission_on_an_unpaid_original_row claim
    (Source.native claim frame) (Source.word claim frame)
  · rwa [Source.state_eq]
  · rwa [Source.state_eq]
  · exact selected_resources_are_generated_on_the_same_source claim frame enough

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem an_admitted_actual_reply_has_no_refusal
    (proposal : RawEvent Party Good Port Technology Instrument)
    (admitted : Root.Admitted claim frame proposal) :
    (Refusal.Source.readReply claim frame proposal).refusalWitness? = none := by
  cases returned : (Refusal.Source.readReply claim frame proposal).refusalWitness? with
  | none => rfl
  | some refusal =>
    exact (Refusal.RefusalAt.no_capital_renewal_legitimacy claim _ _ _ _ refusal admitted).elim

theorem sufficient_current_resources_cannot_return_a_refusal
    (declared : (Abolition.Accounting.Root.Reentry.Frame.state claim frame).declared = true)
    (unpaid : ¬ Responsibility.Family.State.isPaid claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame))
    (enough : Adequacy.Compiler.Enough claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members) :
    (actualReply claim frame).refusalWitness? = none :=
  an_admitted_actual_reply_has_no_refusal claim (Source.native claim frame) (Source.word claim frame)
    (sufficient_current_resources_force_actual_renewal_without_an_adoption_choice claim frame declared unpaid enough)

theorem an_empty_source_choice_keeps_every_exact_menu_obstruction
    (missing : (Source.read claim frame).2.1 = none) :
    ∀ candidate ∈ Adequacy.Compiler.plans claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members, ∃ issue,
      Adequacy.Capacity.inspectResources claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
        frame.actualLaw frame.members candidate = .blocked issue := by
  have selected := congrArg (fun packet => packet.2.1) (Source.read_eq claim frame)
  have empty : Adequacy.Compiler.compile claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame)
      frame.actualLaw frame.members = none := selected.symm.trans missing
  exact Adequacy.Compiler.inspect_menu_from_no_compiled_plan claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim frame) frame.actualLaw frame.members empty

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution
