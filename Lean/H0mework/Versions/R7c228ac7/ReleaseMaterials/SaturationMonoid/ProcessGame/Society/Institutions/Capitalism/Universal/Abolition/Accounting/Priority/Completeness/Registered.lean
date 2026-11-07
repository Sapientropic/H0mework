import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness.Execution.Guarantee
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completion.Assembly

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

/-- Every actual prefix starts from the registered source's fresh liability.
Refusal and funded settlement are consumed on that same returned current. -/
theorem the_original_registered_root_is_refusal_accounted_and_resource_complete
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (claim : Responsibility.Family.Claim mechanism past nature response)
    (origin : Abolition.Accounting.Root.Source.OriginAt input
      (Financial.Installation.Runtime.frames input depth count).native
      ((Financial.Installation.Runtime.frames input depth count).temporal input) claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    let fresh := Abolition.Accounting.Completion.currentFamily input depth count claim []
    let current := Root.afterInputs claim fresh inputs
    let original := Completion.responsibility_is_paid_before_capital_and_has_no_unbounded_renewal_authority
      input depth count claim origin []
    Completion.RegisteredPriorityAt input depth count claim origin [] ∧
      (∀ proposal, Refusal.RefusalInstalledAt claim current proposal) ∧
      (∀ proposal (resources : Adequacy.Capacity.Resources claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim current) current.actualLaw current.members proposal),
        type_of% (every_resource_sufficient_original_programme_actually_settles_the_same_root claim current proposal
          (original.every_continuation_declared inputs) resources)) ∧
      ∀ enough : Adequacy.Compiler.Enough claim
        (Abolition.Accounting.Root.Reentry.Frame.state claim current) current.actualLaw current.members,
        type_of% (Execution.sufficient_current_resources_force_actual_whole_ledger_payment claim current
          (original.every_continuation_declared inputs) enough) := by
  let fresh := Abolition.Accounting.Completion.currentFamily input depth count claim []
  let current := Root.afterInputs claim fresh inputs
  have original := Completion.responsibility_is_paid_before_capital_and_has_no_unbounded_renewal_authority
    input depth count claim origin []
  refine ⟨original,?_,?_,?_⟩
  · intro proposal
    exact Refusal.the_original_root_returns_refusal_liability_and_no_capital_renewal_authority claim current proposal
  · intro proposal resources
    exact every_resource_sufficient_original_programme_actually_settles_the_same_root claim current proposal
      (original.every_continuation_declared inputs) resources
  · intro enough
    exact Execution.sufficient_current_resources_force_actual_whole_ledger_payment claim current
      (original.every_continuation_declared inputs) enough

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completeness
