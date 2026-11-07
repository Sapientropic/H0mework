import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Consequences

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

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

local notation "source" => Renewal.native claim frame proposal
local notation "executed" => Gate.executableWord claim frame proposal
local notation "action" => Abolition.Accounting.Root.Reentry.generated claim source executed
local notation "next" => Installation.successor claim frame proposal
local notation "oldState" => Abolition.Accounting.Root.Reentry.Frame.state claim frame
local notation "newState" => Abolition.Accounting.Root.Reentry.Frame.state claim next

structure SourcePriorityAt : Prop where
  source_input : Input.readProposal claim frame proposal = proposal
  source_context : readContext claim (Input.native claim frame proposal) = (frame.actualLaw,frame.members)
  source_gate : Gate.readEvaluation claim frame proposal = Policy.evaluate claim
    (Abolition.Accounting.Root.Reentry.Frame.state claim (Input.native claim frame proposal))
    (readLaw claim (Input.native claim frame proposal))
    (readMembers claim (Input.native claim frame proposal))
    (Input.readProposal claim frame proposal)
  actual_compilation : (Installation.state claim frame proposal).compileInquiry PUnit.unit = .actualAction action
  initial_support : Abolition.Accounting.Root.Reentry.Frame.support claim source =
    Abolition.Accounting.Root.Reentry.Frame.support claim frame
  actual_next : (RootInquiryProcessNode.answered (Installation.presentation claim frame proposal) PUnit.unit).erase =
    (⟨DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
      ⟨(next).V,(next).root.toAuthoritativeRoot,(next).visit⟩⟩ : AnyAuthoritativeRootCurrent)
  actual_prefix : newState = Responsibility.Family.State.advance claim oldState frame.actualLaw executed
  policy_update : newState = (evaluation claim frame proposal).updated
  actual_accepted_word : (Responsibility.Family.State.attempt claim oldState frame.actualLaw executed).actualWord = executed
  actual_inventory : ∀ item ∈ frame.actualLaw.rawItems (oldState).raw executed,
    frame.actualLaw.Valid item.before item.request
  actual_raw_execution : (newState).raw = frame.actualLaw.next (oldState).raw executed
  same_world : (action).target.TargetN = DebtActivationWorld.ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)
  whole_ledger : type_of% (Installation.all_original_ledger_keys_are_preserved claim frame proposal)
  inherited_support : (Abolition.Accounting.Root.Reentry.Frame.support claim next).1 =
    (Abolition.Accounting.Root.Reentry.Frame.support claim frame).1
  original_row : (next).row.1 = .inr (Responsibility.Family.activationLaw claim).debtId
  no_refill : ∀ key,(newState).remaining key ≤ (oldState).remaining key
  original_claims : (newState).raw.claims = (oldState).raw.claims
  inherited_gate : HEq (Installation.successorGateFace claim frame proposal).rootRead (evaluation claim frame proposal)
  inherited_renewal : HEq (Installation.successorRenewalFace claim frame proposal).rootRead (renewalDecision claim frame proposal)
  visible_needs : HEq (successorNeedsFace claim frame proposal).rootRead
    (Responsibility.Family.inspectActualNeeds claim oldState frame.actualLaw executed frame.members)
  actual_residual : match renewalDecision claim frame proposal with
    | .residual issue _ => 0 < (newState).remaining issue.key
    | .admitted .. | .settled .. | .gate .. | .needs .. => True

/-- One source evaluation controls the actual action, its complete old ledger,
the original native debt row and the returned context for the next input. -/
theorem the_original_row_executes_its_source_generated_priority_gate :
    SourcePriorityAt claim frame proposal where
  source_input := Input.readProposal_eq claim frame proposal
  source_context := Input.context_read_is_the_original_source_context claim frame proposal
  source_gate := rfl
  actual_compilation := Installation.compiler_executes_only_the_source_gate_word claim frame proposal
  initial_support := Installation.source_support_is_literal claim frame proposal
  actual_next := Installation.actual_next_is_the_same_whole_ledger_successor claim frame proposal
  actual_prefix := Installation.successor_reads_the_actual_prefix_update claim frame proposal
  policy_update := Installation.successor_is_the_policy_update claim frame proposal
  actual_accepted_word := Installation.the_actual_accepted_word_is_the_original_executable_word claim frame proposal
  actual_inventory := Installation.every_executed_item_is_valid_in_the_original_physical_inventory claim frame proposal
  actual_raw_execution := Installation.actual_next_runs_the_original_physical_law_on_the_entire_accepted_prefix claim frame proposal
  same_world := rfl
  whole_ledger := Installation.all_original_ledger_keys_are_preserved claim frame proposal
  inherited_support := Installation.the_old_network_support_is_retained claim frame proposal
  original_row := Installation.the_native_liability_keeps_its_original_key claim frame proposal
  no_refill := by
    rw [Installation.successor_reads_the_actual_prefix_update]
    exact Responsibility.Family.State.actual_advance_never_refills_any_original_cell claim _ _ _
  original_claims := Installation.no_original_financial_claim_is_erased claim frame proposal
  inherited_gate := Installation.successor_gate_is_the_literal_source_decision claim frame proposal
  inherited_renewal := Installation.successor_renewal_is_the_literal_source_verdict claim frame proposal
  visible_needs := the_next_need_face_retains_the_actual_original_bearers claim frame proposal
  actual_residual := Installation.the_generated_residual_is_positive_in_the_actual_next claim frame proposal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
