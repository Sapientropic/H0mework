import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewHandoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 128000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ConcreteProductiveSource (base laws)
noncomputable section

def predecessorModel := DeferredProviderSource.model
def predecessorPoint := (DeferredProviderSource.trace true).cursor
def predecessorSeed := (DeferredProviderSource.trace true).before
def model := CompletionReviewHandoff.modelAfter predecessorModel predecessorPoint predecessorSeed
def origin := CompletionReviewHandoff.point predecessorModel predecessorPoint predecessorSeed
def before := CompletionReviewHandoff.after predecessorModel predecessorSeed

def control (receiptPresent : Bool) (trace : SourceContinuationTrace.Trace model) : LocalCommandSource.Input :=
 if CompletionReviewHandoff.offered model trace.before receiptPresent then
  match (List.range model.source.code.actions.length).find?
   (fun index => decide (model.source.code.actions[index]?=some (CompletionReviewHandoff.request model trace.before))) with
  | none => .idle
  | some index => .command index
 else .idle

def trace := SourceOpportunityHandoff.controlled model origin before (control CompletionReviewHandoff.receiptReady) 2
def withoutReceipt := SourceOpportunityHandoff.controlled model origin before (control false) 2
def replay := SourceOpportunityHandoff.controlled model trace.cursor trace.before (control CompletionReviewHandoff.receiptReady) 2

def vocabulary := SuccessorSigningSource.vocabulary model origin base
def reception : StageReception.Law model.source.code :=
 ⟨fun receiver current => {(laws model).scope receiver current with phase := origin.cut},64⟩
def scope := {ConcreteProductiveSource.scope with phase := origin.cut}
def receiver : Fin model.source.code.sites := ⟨2,by change 2<3;decide⟩
def ledger := CachedWorkDispatch.ledger vocabulary trace.rows
def decision := CachedWorkDispatch.produce vocabulary origin reception trace.rows receiver scope 1

theorem actual_completion_and_live_native_admission_generate_the_review_offer :
 CompletionReviewHandoff.receiptReady=true ∧ CompletionReviewHandoff.invoiceEpoch=0 ∧
 CompletionReviewHandoff.offered predecessorModel predecessorSeed CompletionReviewHandoff.receiptReady=true ∧
 before.current.technology.version=0 ∧ before.current.stock 1 .service=1 := by
 and_intros <;> decide +kernel

theorem the_actual_paid_review_changes_the_native_epoch_and_preserves_debt :
 trace.before.current.technology.version=1 ∧ trace.before.current.technology.last=some (.review) ∧
 trace.before.current.stock 1 .service=0 ∧ trace.before.remaining=38 ∧
 (∀ instrument debtor creditor,trace.before.current.claims instrument debtor creditor=predecessorSeed.current.claims instrument debtor creditor) ∧
 trace.rows.any (fun row => decide (row.submitted=[CompletionReviewHandoff.request model before]))=true := by
 and_intros <;> decide +kernel

theorem deleting_the_actual_completion_blocks_this_review_protocol :
 withoutReceipt.before.current.technology.version=0 ∧ withoutReceipt.before.current.stock 1 .service=1 := by
 and_intros <;> decide +kernel

theorem the_old_invoice_epoch_is_stale_after_the_actual_review :
 CompletionReviewHandoff.fresh model trace.before=false ∧
 control CompletionReviewHandoff.receiptReady trace=LocalCommandSource.Input.idle ∧
 replay.before.current.technology.version=1 ∧ replay.before.current.stock 1 .service=0 ∧
 ¬model.source.code.law.Valid trace.before.current (CompletionReviewHandoff.request model before) := by
 and_intros <;> decide +kernel

theorem the_wrong_reviewer_has_no_original_native_permission :
 ¬Mandate.CanRun model.scope before.current 2 (.review) ∧
 ¬model.source.code.law.Valid before.current (Mandate.request model.scope before.current 2 (.review)) := by
 and_intros <;> decide +kernel

theorem the_native_review_has_a_paid_new_phase_ballot_but_no_free_decision :
 ledger.isEmpty=false ∧ (ledger.all fun ballot => decide (ballot.choice=true ∧ ballot.scope.phase=origin.cut))=true ∧
 decision=.blocked .missingQuorum := by and_intros <;> decide +kernel

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewSource
