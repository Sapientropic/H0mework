import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws contract)
open RecoveredProductiveSource (recycling feeding)
open SourceCreditSource
open private SourceOpportunityConsumer.predecessor_original from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunityConsumer
noncomputable section

local notation "oldFirst" => (FreshSigningSource.cycle contract base laws ConcreteProductiveSource.ready ConcreteProductiveSource.request)
local notation "oldDonation" => (JointReceptionSource.advance recycling oldFirst (RenewableArchiveSource.Command.renew false true))
local notation "oldSupply" => (JointReceptionSource.advance feeding oldDonation (RenewableArchiveSource.Command.renew true true))
local notation "oldReady" => (JointReceptionSource.advance contract oldSupply (RenewableArchiveSource.Command.execute [LocalCommandSource.Input.command 2,LocalCommandSource.Input.idle]))
local notation "oldPrepared" => (FreshSigningSource.prepared contract oldReady ConcreteProductiveSource.request)
local notation "oldPredecessor" => (FreshSigningSource.next contract base laws oldPrepared ConcreteProductiveSource.request)
local notation "oldRegistered" => (SourceOpportunityHandoff.register oldPredecessor)
local notation "predecessor" => (JointReceptionSource.advance contract oldRegistered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceOpportunitySource.trace)))

local notation "registered" => (SourceCreditHandoff.register predecessor)
local notation "issuedState" => (JointReceptionSource.advance contract registered (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs SourceCreditSource.issued)))
local notation "funded" => (JointReceptionSource.advance exchange issuedState (RenewableArchiveSource.Command.renew true true))
local notation "nextState" => (JointReceptionSource.advance contract funded (RenewableArchiveSource.Command.execute (SourceContinuationTrace.Trace.inputs (SourceCreditSource.trace true))))

theorem the_predecessor_is_the_complete_original_seed : predecessorSeed=EventStep.seed predecessorPoint :=
 SourceOpportunityConsumer.the_generated_control_is_the_original_actual_execution.2.1

theorem the_predecessor_is_the_complete_original_occurrence :
 FreshSigningReplay.physical (predecessor).actual=⟨predecessorModel,predecessorPoint⟩ :=
 SourceOpportunityConsumer.the_actual_next_keeps_the_entire_original_model_and_generated_cursor

private theorem predecessor_original : predecessorPoint.side=.original :=
 (SourceOpportunityHandoff.controlled_keeps_the_source_side SourceOpportunitySource.model SourceOpportunitySource.origin
  SourceOpportunitySource.before (SourceOpportunitySource.control SourceOpportunitySource.model SourceOpportunitySource.origin) 36).trans
  SourceOpportunityConsumer.predecessor_original

private theorem credit_original : creditPoint.side=.original := predecessor_original

theorem the_registered_credit_seed_is_the_entire_original_extended_seed : creditSeed=EventStep.seed creditPoint :=
 SourceCreditHandoff.after_is_the_entire_actual_extended_seed predecessorModel predecessorPoint predecessorSeed
  the_predecessor_is_the_complete_original_seed predecessor_original

theorem the_registered_credit_is_the_complete_original_occurrence :
 FreshSigningReplay.physical (registered).actual=⟨creditModel,creditPoint⟩ :=
 SourceCreditHandoff.registration_at_the_same_complete_cached_occurrence predecessorModel predecessorPoint predecessorSeed
  predecessor the_predecessor_is_the_complete_original_occurrence the_predecessor_is_the_complete_original_seed

theorem the_credit_issue_replays_its_actual_source_inputs :
 SourceContinuationTrace.Sound creditModel creditPoint issued (LocalCommandRun.run creditModel creditPoint issued.inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs creditModel creditPoint creditSeed
  the_registered_credit_seed_is_the_entire_original_extended_seed (borrower creditModel) 2

private theorem issued_original : issued.cursor.side=.original :=
 (SourceOpportunityHandoff.controlled_keeps_the_source_side creditModel creditPoint creditSeed (borrower creditModel) 2).trans credit_original

theorem the_actual_issued_credit_is_the_complete_original_occurrence :
 FreshSigningReplay.physical (issuedState).actual=⟨creditModel,issued.cursor⟩ :=
 SourceCreditHandoff.controlled_execution_keeps_the_entire_actual_occurrence creditModel creditPoint creditSeed
  contract registered the_registered_credit_is_the_complete_original_occurrence
  the_registered_credit_seed_is_the_entire_original_extended_seed (borrower creditModel) 2

theorem the_funded_seed_is_the_entire_actual_window_endpoint (accept : Bool) : before accept=EventStep.seed (origin accept) :=
 SourceWindowCache.after_is_the_entire_actual_endpoint creditModel.source.code exchange issued.cursor issued.before true accept
  the_credit_issue_replays_its_actual_source_inputs.2.1 issued_original

theorem the_funded_model_is_the_entire_actual_window_occurrence (accept : Bool) :
 FreshSigningReplay.physical (JointReceptionSource.advance exchange issuedState (.renew true accept)).actual=⟨model accept,origin accept⟩ :=
 SourceWindowCache.renewal_at_the_same_complete_cached_occurrence exchange true accept (issuedState).actual
  creditModel issued.cursor issued.before the_actual_issued_credit_is_the_complete_original_occurrence
  the_credit_issue_replays_its_actual_source_inputs.2.1 issued_original

theorem the_window_admission_is_the_original_actual_guard (accept : Bool) :
 PaidInvocationSource.admitted (issuedState).actual.model.source.code exchange (issuedState).actual.point true accept=
 SourceWindowCache.admitted creditModel.source.code exchange issued.cursor issued.before true accept :=
 SourceWindowCache.admission_at_the_same_complete_cached_occurrence exchange true accept (issuedState).actual
  creditModel issued.cursor issued.before the_actual_issued_credit_is_the_complete_original_occurrence
  the_credit_issue_replays_its_actual_source_inputs.2.1 issued_original

theorem only_the_actual_paid_provider_branch_opens_the_original_window :
 PaidInvocationSource.admitted (issuedState).actual.model.source.code exchange (issuedState).actual.point true true=true ∧
 PaidInvocationSource.admitted (issuedState).actual.model.source.code exchange (issuedState).actual.point true false=false :=
 ⟨(the_window_admission_is_the_original_actual_guard true).trans real_waste_and_provider_payout_open_the_actual_new_window.1,
  (the_window_admission_is_the_original_actual_guard false).trans missing_provider_retains_new_debt_but_cannot_open_the_window_or_decide.1⟩

theorem the_communication_replays_its_actual_source_inputs (accept : Bool) :
 SourceContinuationTrace.Sound (model accept) (origin accept) (trace accept)
  (LocalCommandRun.run (model accept) (origin accept) (trace accept).inputs) :=
 SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs (model accept) (origin accept) (before accept)
  (the_funded_seed_is_the_entire_actual_window_endpoint accept) (control accept) 18

theorem the_new_receiver_is_the_original_independent_consumer (accept : Bool) :
 observed accept=HeaderReception.run (vocabulary accept) (reception accept) (origin accept)
  (trace accept).stages (receiver accept) (trace accept).stages.length :=
 SourceContinuationTrace.receiver_from_the_same_complete_actual_trace (model accept) (origin accept) (trace accept) _
  (the_communication_replays_its_actual_source_inputs accept) (vocabulary accept) (reception accept) (receiver accept)

theorem the_financed_decision_is_the_original_authenticated_quorum :
 HeaderQuorum.produce (origin true) (vocabulary true) (reception true) (trace true).stages (receiver true) (scope true) 1=.decided true := by
 have sound := the_communication_replays_its_actual_source_inputs true
 have rows := sound.2.2.1.trans (congrArg (StageTrace.records (origin true)) sound.2.2.2.2.symm)
 have same := CachedWorkDispatch.produce_eq (vocabulary true) (origin true) (reception true)
  (trace true).stages (receiver true) (scope true) 1
 have checked := congrArg (fun rows : List (StageTrace.Record (code := (model true).source.code)) =>
  CachedWorkDispatch.produce (vocabulary true) (origin true) (reception true) rows (receiver true) (scope true) 1) rows.symm
 exact same.symm.trans (checked.trans the_financed_phase_generates_a_new_actual_authenticated_decision.1)

theorem every_new_receipt_has_its_original_paid_ballot
 (receipt : HeaderReception.Receipt (code := (model true).source.code)) (inside : receipt∈(observed true).receipts) :
 receipt.wire.ballot∈StageBudget.ledger (vocabulary true) (origin true) (trace true).stages :=
 HeaderReception.receipt_has_original_paid_ballot (vocabulary true) (reception true) (origin true)
  (trace true).stages (receiver true) (trace true).stages.length receipt
  (Eq.mp (congrArg (fun received : HeaderReception.Receiver (code := (model true).source.code) => receipt∈received.receipts)
   (the_new_receiver_is_the_original_independent_consumer true)) inside)

theorem the_actual_next_keeps_the_entire_original_model_and_generated_cursor :
 FreshSigningReplay.physical (nextState).actual=⟨model true,(trace true).cursor⟩ :=
 SourceCreditHandoff.controlled_execution_keeps_the_entire_actual_occurrence (model true) (origin true) (before true)
  contract funded (the_funded_model_is_the_entire_actual_window_occurrence true)
  (the_funded_seed_is_the_entire_actual_window_endpoint true) (control true) 18

theorem the_actual_next_has_the_generated_entire_current :
 (EventStep.seed (nextState).actual.point).current=(trace true).before.current :=
 SourceContinuationTrace.current_from_the_same_complete_occurrence (model true) (trace true).cursor (nextState).actual
  (trace true).before the_actual_next_keeps_the_entire_original_model_and_generated_cursor
  (the_communication_replays_its_actual_source_inputs true).2.1

theorem the_actual_next_keeps_the_new_debt_and_production_obstruction :
 (∀ instrument debtor creditor,(EventStep.seed (nextState).actual.point).current.claims instrument debtor creditor=
 predecessorSeed.current.claims instrument debtor creditor+(if debtor=1 ∧ creditor=2 then 3 else 0)) ∧
 ¬(model true).source.code.law.Valid (EventStep.seed (nextState).actual.point).current RecycledQuorumMaterial.production :=
 Eq.mp (congrArg (fun current : RecycledQuorumMaterial.Current =>
  (∀ instrument debtor creditor,current.claims instrument debtor creditor=predecessorSeed.current.claims instrument debtor creditor+
   (if debtor=1 ∧ creditor=2 then 3 else 0)) ∧ ¬(model true).source.code.law.Valid current RecycledQuorumMaterial.production)
  the_actual_next_has_the_generated_entire_current.symm)
  successful_communication_keeps_the_actual_new_debt_and_material_obstruction

theorem the_actual_financed_cycle_keeps_all_history_responsibility_and_own_next :
 (predecessor).actual.archive <+: (nextState).actual.archive ∧ (predecessor).actual.windows <+: (nextState).actual.windows ∧
 (predecessor).rows <+: (nextState).rows ∧ ArchivedDeliveryConsumer.NativeContinuation (nextState).actual.model (nextState).actual.point :=
 SourceCreditHandoff.the_financed_cycle_keeps_history_responsibility_and_own_next contract exchange predecessor issued.inputs (trace true).inputs true

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceCreditConsumer
