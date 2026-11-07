import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Completion.Assembly
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Inspection
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Entitlements.Redemption

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}

local instance registeredProjectionFinite
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat) :
    Finite (Financial.Installation.Runtime.frames input depth count).native.root.toAuthoritativeRoot.source.projectionLaw.Projection :=
  (Financial.Installation.Runtime.frames input depth count).projectionFinite

omit [DecidableEq Port] in
private theorem law_after_inputs
    (claim : Responsibility.Family.Claim mechanism past nature response) {oldN : WorldRelationNetwork}
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    (Root.afterInputs claim frame inputs).actualLaw = frame.actualLaw := by
  induction inputs generalizing frame with
  | nil => rfl
  | cons proposal rest ih =>
      exact (ih (Root.Installation.successor claim frame proposal)).trans rfl

omit [DecidableEq Port] in
private theorem declaration_after_inputs
    (claim : Responsibility.Family.Claim mechanism past nature response) {oldN : WorldRelationNetwork}
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    (Abolition.Accounting.Root.Reentry.Frame.state claim (Root.afterInputs claim frame inputs)).declared =
      (Abolition.Accounting.Root.Reentry.Frame.state claim frame).declared := by
  induction inputs generalizing frame with
  | nil => rfl
  | cons proposal rest ih =>
    change (Abolition.Accounting.Root.Reentry.Frame.state claim
      (Root.afterInputs claim (Root.Installation.successor claim frame proposal) rest)).declared = _
    rw [ih,Root.Installation.successor_reads_the_actual_prefix_update]
    rfl

/-- Every argument is an original source datum. No section notation captures a
second first input or a caller-selected current behind this contract. -/
structure RegisteredPriorityAt
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (claim : Responsibility.Family.Claim mechanism past nature response)
    (origin : Abolition.Accounting.Root.Source.OriginAt input
      (Financial.Installation.Runtime.frames input depth count).native
      ((Financial.Installation.Runtime.frames input depth count).temporal input) claim)
    (firstInput : RawEvent Party Good Port Technology Instrument) : Prop where
  original_account : Abolition.Accounting.Root.Action.Runtime.SameSourceAccountingAt
    input (Financial.Installation.Runtime.frames input depth count).native
    ((Financial.Installation.Runtime.frames input depth count).temporal input) claim origin firstInput
    (Financial.Installation.Runtime.frames input depth count).authority
  unique_origins : ((Epoch.Finance.Legacy.generated input 0 0
    ((Financial.Installation.Runtime.frames input depth count).cursor input).account).current.slots.map
    (fun slot => (Epoch.Finance.slotClaim input 0 0 slot).origin input 0 0)).Nodup
  finite_original_contribution : Contribution.OriginalClaimBounded input 0 0
    (Epoch.Finance.Legacy.generated input 0 0
      ((Financial.Installation.Runtime.frames input depth count).cursor input).account).current
  original_current : Abolition.Accounting.Root.Reentry.Frame.state claim
      (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) =
    Abolition.Accounting.Root.Source.observed input (Financial.Installation.Runtime.frames input depth count).native
      ((Financial.Installation.Runtime.frames input depth count).temporal input) claim firstInput
  current_declared : (Abolition.Accounting.Root.Reentry.Frame.state claim
    (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput)).declared = true
  every_continuation_declared : ∀ inputs, (Abolition.Accounting.Root.Reentry.Frame.state claim
    (Root.afterInputs claim (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs)).declared = true
  source_law : (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput).actualLaw =
    Abolition.Accounting.Root.Source.actualLaw input
  no_control_veto : ∀ technology port actor,
    (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput).actualLaw.allowed technology port actor = true
  no_control_reintroduced : ∀ inputs technology port actor,
    (Root.afterInputs claim (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs).actualLaw.allowed
      technology port actor = true
  every_actual_input : ∀ proposal, Root.SourcePriorityAt claim
    (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) proposal
  every_actual_continuation : ∀ inputs proposal,
    Root.SourcePriorityAt claim (Root.afterInputs claim
      (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs) proposal
  no_capitalization_of_old_authority : ∀ inputs proposal,
    let frame := Root.afterInputs claim (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs
    let word := Root.Gate.executableWord claim frame proposal
    (∀ request ∈ word, ¬ Policy.FinancialOperation request.operation) ∧
      (Responsibility.Family.State.isPaid claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame) →
        ∀ request ∈ word, ¬ Policy.CompulsoryTake request.operation) ∧
      ∀ terms, ¬ Nonempty (PublicFunction.Financing.Disbursement frame.actualLaw
        (Abolition.Accounting.Root.Reentry.Frame.state claim frame).raw word terms)
  no_debt_finality : ∀ inputs,
    (Responsibility.Family.activationLaw claim).SupportTerminalAt
      (Abolition.Accounting.Root.Reentry.Frame.state claim (Root.afterInputs claim
        (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs)) → False
  finite_admission : ∀ inputs,
    Root.AllAdmitted claim (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs →
    inputs.length + Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim
      (Root.afterInputs claim (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs)) ≤
      Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim
        (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput))
  finite_stop : ∀ inputs
    (longer : Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim
      (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput)) < inputs.length),
    let stop := Root.finiteStop claim (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput) inputs longer
    stop.priorInputs.length ≤ Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim
      (Abolition.Accounting.Completion.currentFamily input depth count claim firstInput)) ∧
      Root.SourcePriorityAt claim stop.current stop.proposal

/-- The original account and every actual continuation share one explicit
registered source and the one first input supplied here. -/
theorem responsibility_is_paid_before_capital_and_has_no_unbounded_renewal_authority
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (claim : Responsibility.Family.Claim mechanism past nature response)
    (origin : Abolition.Accounting.Root.Source.OriginAt input
      (Financial.Installation.Runtime.frames input depth count).native
      ((Financial.Installation.Runtime.frames input depth count).temporal input) claim)
    (firstInput : RawEvent Party Good Port Technology Instrument) :
    RegisteredPriorityAt input depth count claim origin firstInput := by
  let active := Abolition.Accounting.Completion.currentFamily input depth count claim firstInput
  have old := Abolition.Accounting.Completion.the_registered_root_carries_its_complete_account_into_each_actual_next_input
    input depth count claim origin firstInput
  have declared : (Abolition.Accounting.Root.Reentry.Frame.state claim active).declared = true := by
    rw [Abolition.Accounting.Completion.current_family_is_the_actual_observed_row]
    rfl
  exact {
    original_account := old.1
    unique_origins := old.2.1
    finite_original_contribution := old.2.2.1
    original_current := old.2.2.2.1
    current_declared := declared
    every_continuation_declared := fun inputs => (declaration_after_inputs claim active inputs).trans declared
    source_law := rfl
    no_control_veto := fun _ _ _ => rfl
    no_control_reintroduced := fun inputs technology port actor =>
      (congrArg (fun law => law.allowed technology port actor)
        (law_after_inputs claim active inputs)).trans rfl
    every_actual_input := fun proposal =>
      Root.the_original_row_executes_its_source_generated_priority_gate claim active proposal
    every_actual_continuation := fun inputs proposal =>
      Root.the_original_row_executes_its_source_generated_priority_gate claim
        (Root.afterInputs claim active inputs) proposal
    no_capitalization_of_old_authority := fun inputs proposal =>
      ⟨Entitlements.the_original_repair_authority_cannot_be_capitalized_as_a_financial_operation
          claim (Root.afterInputs claim active inputs) proposal,
        Entitlements.a_cleared_original_row_cannot_renew_any_compulsory_take
          claim (Root.afterInputs claim active inputs) proposal,
        Entitlements.no_real_disbursement_can_be_minted_by_redeeming_the_old_repair_row
          claim (Root.afterInputs claim active inputs) proposal⟩
    no_debt_finality := fun _ impossible => nomatch impossible
    finite_admission := fun inputs admitted =>
      Root.the_original_current_bounds_every_actual_admitted_sequence claim active inputs admitted
    finite_stop := fun inputs longer =>
      ⟨(Root.finiteStop claim active inputs longer).priorInputs_bounded,
        (Root.finiteStop claim active inputs longer).the_stopped_actual_input_keeps_its_whole_ledger_and_generated_next⟩ }

omit [DecidableEq Port] in
private theorem empty_repair_keeps_every_original_remaining_cell
    (claim : Responsibility.Family.Claim mechanism past nature response)
    (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument) :
    (Responsibility.Family.State.advance claim state law []).remaining = state.remaining := by
  funext key
  simp only [Responsibility.Family.State.advance,Responsibility.Family.State.attempt,
    Responsibility.Family.inspectAttempt,Responsibility.Family.inspectSource,Responsibility.inspectMaterial,
    Responsibility.Family.Attempt.credit,RawLaw.rawItems,RawLaw.next,RawLaw.execute,sub_self,max_self,sub_zero]
  exact max_eq_right (state.nonnegative key)

/-- The canonical fresh entry installs priority before any repair cash flow.
The old-source first input is empty, and the original unpaid matrix is unchanged. -/
theorem the_fresh_registered_root_installs_priority_before_any_repair
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (claim : Responsibility.Family.Claim mechanism past nature response)
    (origin : Abolition.Accounting.Root.Source.OriginAt input
      (Financial.Installation.Runtime.frames input depth count).native
      ((Financial.Installation.Runtime.frames input depth count).temporal input) claim) :
    RegisteredPriorityAt input depth count claim origin [] ∧
      (∀ key, (Abolition.Accounting.Root.Reentry.Frame.state claim
        (Abolition.Accounting.Completion.currentFamily input depth count claim [])).remaining key =
          Responsibility.Family.quantity mechanism past nature response key) ∧
      ¬ Responsibility.Family.State.isPaid claim (Abolition.Accounting.Root.Reentry.Frame.state claim
        (Abolition.Accounting.Completion.currentFamily input depth count claim [])) := by
  have same : (Abolition.Accounting.Root.Reentry.Frame.state claim
      (Abolition.Accounting.Completion.currentFamily input depth count claim [])).remaining =
      (Abolition.Accounting.Root.Source.initialState input
        (Financial.Installation.Runtime.frames input depth count).native
        ((Financial.Installation.Runtime.frames input depth count).temporal input) claim).remaining := by
    rw [Abolition.Accounting.Completion.current_family_is_the_actual_observed_row]
    exact empty_repair_keeps_every_original_remaining_cell claim _ _
  refine ⟨responsibility_is_paid_before_capital_and_has_no_unbounded_renewal_authority input depth count claim origin [],?_,?_⟩
  · intro key
    rw [same]
    exact Responsibility.Family.State.admission_remaining_is_the_positive_source_quantity claim _ key
  · intro paid
    have original : Responsibility.Family.State.isPaid claim
        (Abolition.Accounting.Root.Source.initialState input
          (Financial.Installation.Runtime.frames input depth count).native
          ((Financial.Installation.Runtime.frames input depth count).temporal input) claim) := by
      intro key member
      rw [← same]
      exact paid key member
    exact Responsibility.Family.State.atCursor_is_unpaid claim _ original

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Completion
