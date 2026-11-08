import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeferredProviderConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewHandoff
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open private RenewableArchiveSource.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveSource
open private JointReceptionSource.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionSource

abbrev Model := FreshSigningReplay.Model (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)
abbrev Action := RecycledQuorumMaterial.Action
def invoiceEpoch := DeferredProviderReceipt.payment.before.current.technology.version
def receiptReady : Bool := match DeferredProviderReceipt.produce true with | .completed _ => true | .pending => false
variable (model : Model) (saved : Cursor model.source.code) (retained : Feedback.State model.source.code)

def request : Action := Mandate.request model.scope retained.current DeferredProviderReceipt.bill.payer .review
def fresh : Bool := decide (retained.current.technology.version=invoiceEpoch)
def offered (receiptPresent : Bool) : Bool := receiptPresent && fresh model retained &&
 decide (model.source.code.law.Valid retained.current (request model retained))
def catalogue (receiptPresent : Bool) : CatalogueHandoffSource.Catalogue model.source.code :=
 ⟨if offered model retained receiptPresent then [request model retained] else [],1,[],0,
 (List.finRange model.source.code.sites).map Event.activate⟩
def point := CatalogueHandoffSource.cursor model.source.code (catalogue model retained receiptReady) saved
def after : Feedback.State (CatalogueHandoffSource.code model.source.code (catalogue model retained receiptReady)) :=
 Extension.state model.source.code (CatalogueHandoffSource.supply model.source.code (catalogue model retained receiptReady)) retained
def modelAfter : Model :=
 ⟨model.base,model.scope,(point model saved retained).source,model.law_exact,model.task_exact⟩
def output : FreshSigningReplay.Physical (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit) :=
 ⟨modelAfter model saved retained,point model saved retained⟩

variable {root : RenewableCodeLineage.Emitter (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit)}
def register (state : JointReceptionSource.State root) : JointReceptionSource.State root :=
 let extra := catalogue state.actual.model (EventStep.seed state.actual.point) receiptReady
 JointReceptionSource.State.mk
  (RenewableArchiveSource.State.mk (modelAfter state.actual.model state.actual.point (EventStep.seed state.actual.point))
   (point state.actual.model state.actual.point (EventStep.seed state.actual.point)) state.actual.archive state.actual.windows)
  (.extended state.lineage extra) state.rows

theorem offered_requires_actual_pairing_freshness_and_native_admission
 (receiptPresent : Bool) (yes : offered model retained receiptPresent=true) :
 receiptPresent=true ∧ fresh model retained=true ∧ model.source.code.law.Valid retained.current (request model retained) := by
 simp only [offered,Bool.and_eq_true] at yes
 exact ⟨yes.1.1,yes.1.2,of_decide_eq_true yes.2⟩

theorem a_changed_native_epoch_blocks_the_old_invoice_independently_of_resources
 (receiptPresent : Bool) (changed : retained.current.technology.version≠invoiceEpoch) :
 offered model retained receiptPresent=false := by
 apply Bool.eq_false_iff.mpr
 intro accepted
 have current := (offered_requires_actual_pairing_freshness_and_native_admission
  model retained receiptPresent accepted).2.1
 exact changed (of_decide_eq_true current)

theorem registration_at_the_same_complete_cached_occurrence
 (state : JointReceptionSource.State root)
 (physical : FreshSigningReplay.physical state.actual=⟨model,saved⟩) (same : retained=EventStep.seed saved) :
 FreshSigningReplay.physical (register state).actual=output model saved retained := by
 cases state
 rename_i actual lineage rows
 cases actual
 cases physical
 subst retained
 rfl

theorem after_is_the_entire_actual_extended_seed
 (same : retained=EventStep.seed saved) (original : saved.side=.original) :
 after model retained=EventStep.seed (point model saved retained) :=
 (congrArg (Extension.state model.source.code
  (CatalogueHandoffSource.supply model.source.code (catalogue model retained receiptReady))) same).trans
   (CatalogueHandoffSource.seed model.source.code (catalogue model retained receiptReady) saved original).symm

theorem registration_retains_the_original_law_task_identity_and_budget (state : JointReceptionSource.State root) :
 (register state).actual.model.source.code.law=state.actual.model.source.code.law ∧
 (register state).actual.model.source.code.task=state.actual.model.source.code.task ∧
 (register state).actual.model.source.code.siteParty=state.actual.model.source.code.siteParty ∧
 (register state).actual.point.entry.budget=state.actual.point.entry.budget := ⟨rfl,rfl,rfl,rfl⟩

theorem controlled_execution_keeps_the_entire_actual_occurrence
 (contract : PaidInvocationSource.Contract (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit))
 (state : JointReceptionSource.State root)
 (physical : FreshSigningReplay.physical state.actual=⟨model,saved⟩) (same : retained=EventStep.seed saved)
 (control : SourceContinuationTrace.Trace model → LocalCommandSource.Input) (count : Nat) :
 let trace := SourceOpportunityHandoff.controlled model saved retained control count
 FreshSigningReplay.physical (JointReceptionSource.advance contract state (.execute trace.inputs)).actual=⟨model,trace.cursor⟩ := by
 let trace := SourceOpportunityHandoff.controlled model saved retained control count
 have fixed := SourceContinuationTrace.fixed_execution_keeps_the_entire_actual_model_and_cursor
  model saved state.actual retained physical same trace.inputs
 have one := (SourceContinuationTrace.every_fixed_prefix_is_the_same_actual_execution model saved retained same trace.inputs).1
 have two := (SourceOpportunityHandoff.every_controlled_prefix_replays_its_actual_source_inputs
  model saved retained same control count).1
 exact fixed.trans (congrArg (fun cursor => (⟨model,cursor⟩ : FreshSigningReplay.Physical
  (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good) (Port := Delegation.Funded.Port)
  (Technology := Bool) (Instrument := Unit))) (one.trans two.symm))

theorem every_registered_execution_keeps_history_responsibility_and_own_next
 (contract : PaidInvocationSource.Contract (Party := Delegation.Funded.Party) (Good := Repayment.Recovery.Good)
 (Port := Delegation.Funded.Port) (Technology := Bool) (Instrument := Unit))
 (state : JointReceptionSource.State root) (inputs : List LocalCommandSource.Input) :
 let next := JointReceptionSource.advance contract (register state) (.execute inputs)
 state.actual.archive <+: next.actual.archive ∧ state.actual.windows <+: next.actual.windows ∧
 state.rows <+: next.rows ∧ ArchivedDeliveryConsumer.NativeContinuation next.actual.model next.actual.point := by
 have later := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows
  contract (register state) [.execute inputs]
 exact ⟨later.1,later.2.1,later.2.2,
  JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletionReviewHandoff
