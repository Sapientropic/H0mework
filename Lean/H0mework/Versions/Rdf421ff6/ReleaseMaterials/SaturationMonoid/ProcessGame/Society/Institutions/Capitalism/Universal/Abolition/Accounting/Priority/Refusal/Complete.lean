import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal.Consequences

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal

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

local notation "packet" => Source.readReply claim frame proposal
local notation "next" => Action.nextFrame claim frame proposal
local notation "executed" => Root.Gate.executableWord claim frame proposal
local notation "oldState" => Abolition.Accounting.Root.Reentry.Frame.state claim frame
local notation "newState" => Abolition.Accounting.Root.Reentry.Frame.state claim next

structure RefusalInstalledAt : Prop where
  submitted : (packet).submittedWord = proposal
  executable : (packet).executableWord = executed
  original_word : (packet).submittedWord = (packet).executableWord ++ (packet).unexecutedSuffix
  compilation : (Installation.state claim frame proposal).compileInquiry PUnit.unit =
    .actualAction (Action.generated claim frame proposal)
  actual_reply : (Action.generated claim frame proposal).target.answer = packet
  actual_next : (RootInquiryProcessNode.answered (Installation.presentation claim frame proposal) PUnit.unit).erase =
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
      ⟨(next).V,(next).root.toAuthoritativeRoot,(next).visit⟩⟩ : AnyAuthoritativeRootCurrent)
  original_support : (Abolition.Accounting.Root.Reentry.Frame.support claim next).1 =
    (Abolition.Accounting.Root.Reentry.Frame.support claim frame).1
  original_keys : type_of% (every_original_ledger_key_is_retained claim frame proposal)
  original_row : (next).row.1 = .inr (Responsibility.Family.activationLaw claim).debtId
  actual_row : newState = Responsibility.Family.State.advance claim oldState frame.actualLaw executed
  original_claims : (newState).raw.claims = (oldState).raw.claims
  payment : match (packet).liability.payment with
    | .paid _ => Responsibility.Family.State.isPaid claim newState
    | .unpaid key _ _ => key ∈ Responsibility.Family.positiveScope mechanism past nature response ∧
        0 < (newState).remaining key
  independent_needs : HEq (nextNeedsFace claim frame proposal).rootRead (packet).liability.needs
  inherited_reply : HEq (nextReplyFace claim frame proposal).rootRead packet
  authority : AuthorityDispositionAt claim _ _ _ _ (packet).classification
  paid_stays_paid : Responsibility.Family.State.isPaid claim oldState →
    Responsibility.Family.State.isPaid claim newState

/-- The named installer returns the source classification and original
liability in the actual action answer, with its same whole-ledger next. -/
theorem the_original_root_returns_refusal_liability_and_no_capital_renewal_authority :
    RefusalInstalledAt claim frame proposal where
  submitted := (packet).source_submitted.trans (Root.Input.readProposal_eq claim frame proposal)
  executable := (packet).source_executed
  original_word := (packet).whole_word
  compilation := Installation.the_named_installer_compiles_the_actual_structured_reply claim frame proposal
  actual_reply := Action.the_reply_is_the_actual_action_answer claim frame proposal
  actual_next := Installation.the_reply_and_its_next_are_the_same_actual_root_transition claim frame proposal
  original_support := the_entire_original_support_is_literal claim frame proposal
  original_keys := every_original_ledger_key_is_retained claim frame proposal
  original_row := the_original_row_has_not_been_replaced claim frame proposal
  actual_row := the_liability_is_read_on_the_same_actual_next_row claim frame proposal
  original_claims := by
    rw [the_liability_is_read_on_the_same_actual_next_row]
    exact (packet).liability.original_financial_claims
  payment := by
    cases (packet).liability.payment with
    | paid complete => rw [the_liability_is_read_on_the_same_actual_next_row]; exact complete
    | unpaid key original positive =>
        exact ⟨original,by rw [the_liability_is_read_on_the_same_actual_next_row]; exact positive⟩
  independent_needs := the_reply_retains_the_independent_actual_need_bearers claim frame proposal
  inherited_reply := the_actual_next_retains_its_source_reply claim frame proposal
  authority := the_classification_keeps_the_original_renewal_authority claim _ _ _ _ (packet).classification
  paid_stays_paid := by
    intro paid
    rw [the_liability_is_read_on_the_same_actual_next_row]
    exact an_already_paid_row_cannot_generate_a_new_positive_liability claim _ _ _ _ paid (packet).liability

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Refusal
