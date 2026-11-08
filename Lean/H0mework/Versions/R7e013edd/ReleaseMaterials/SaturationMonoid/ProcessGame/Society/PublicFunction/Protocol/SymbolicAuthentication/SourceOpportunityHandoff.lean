import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecoveredSigningConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunityHandoff
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open private RenewableArchiveSource.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveSource
open private JointReceptionSource.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JointReceptionSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (saved : Cursor model.source.code) (retained : Feedback.State model.source.code)

def catalogue : CatalogueHandoffSource.Catalogue model.source.code :=
 ⟨[],0,[],0,(List.range (model.source.code.sites*model.source.code.sites)).map fun offset =>
  .deliver (retained.frame.sent.length+offset)⟩
def point := CatalogueHandoffSource.cursor model.source.code (catalogue model retained) saved
def after : Feedback.State (CatalogueHandoffSource.code model.source.code (catalogue model retained)) :=
 Extension.state model.source.code (CatalogueHandoffSource.supply model.source.code (catalogue model retained)) retained
def modelAfter : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) :=
 ⟨model.base,model.scope,(point model saved retained).source,model.law_exact,model.task_exact⟩
def output : FreshSigningReplay.Physical (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument) := ⟨modelAfter model saved retained,point model saved retained⟩

theorem the_catalogue_is_generated_by_the_original_source
 (same : retained=EventStep.seed saved) : catalogue model retained=SuccessorSigningSource.catalogue model saved := by
 subst retained
 rfl

theorem after_is_the_entire_actual_extended_seed
 (same : retained=EventStep.seed saved) (original : saved.side=.original) :
 after model retained=EventStep.seed (point model saved retained) := by
 exact (congrArg (Extension.state model.source.code
  (CatalogueHandoffSource.supply model.source.code (catalogue model retained))) same).trans
   (CatalogueHandoffSource.seed model.source.code (catalogue model retained) saved original).symm

variable {root : RenewableCodeLineage.Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}

-- Install only the original source-generated event catalogue; retain every historical container.
def register (state : JointReceptionSource.State root) : JointReceptionSource.State root :=
 JointReceptionSource.State.mk
  (RenewableArchiveSource.State.mk (SuccessorSigningSource.model state.actual.model state.actual.point)
   (SuccessorSigningSource.start state.actual.model state.actual.point) state.actual.archive state.actual.windows)
  (.extended state.lineage (SuccessorSigningSource.catalogue state.actual.model state.actual.point)) state.rows

theorem registration_retains_every_original_archive_window_and_row (state : JointReceptionSource.State root) :
 (register state).actual.archive=state.actual.archive ∧ (register state).actual.windows=state.actual.windows ∧
 (register state).rows=state.rows := ⟨rfl,rfl,rfl⟩

theorem registration_retains_the_original_law_task_and_identity_map (state : JointReceptionSource.State root) :
 (register state).actual.model.source.code.law=state.actual.model.source.code.law ∧
 (register state).actual.model.source.code.task=state.actual.model.source.code.task ∧
 (register state).actual.model.source.code.siteParty=state.actual.model.source.code.siteParty := ⟨rfl,rfl,rfl⟩

theorem every_registered_execution_keeps_history_responsibility_and_own_next
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (state : JointReceptionSource.State root) (inputs : List LocalCommandSource.Input) :
 let next := JointReceptionSource.advance contract (register state) (.execute inputs)
 state.actual.archive <+: next.actual.archive ∧ state.actual.windows <+: next.actual.windows ∧
 state.rows <+: next.rows ∧ ArchivedDeliveryConsumer.NativeContinuation next.actual.model next.actual.point := by
 have later := SourceRepairRun.replay_keeps_the_original_archives_windows_and_actual_rows
  contract (register state) [.execute inputs]
 exact ⟨later.1,later.2.1,later.2.2,
  JointReceptionConsumer.each_generated_endpoint_keeps_its_whole_ledger_and_own_next _⟩

theorem registration_at_the_same_complete_cached_occurrence
 (state : JointReceptionSource.State root)
 (physical : FreshSigningReplay.physical state.actual=⟨model,saved⟩)
 (same : retained=EventStep.seed saved) :
 FreshSigningReplay.physical (register state).actual=output model saved retained := by
 cases state
 rename_i actual lineage rows
 cases actual
 cases physical
 subst retained
 rfl

theorem every_registered_future_keeps_the_complete_original_financial_prefix
 (state : JointReceptionSource.State root) (original : state.actual.point.side=.original)
 (stages : List (EventHistory.Stage (code := (register state).actual.model.source.code)))
 (ordinal : Nat) (bounded : ordinal≤EventStep.boundary state.actual.point) :
 Native.Coupling.Match state.actual.model.source.code state.actual.point.source.input
  (EventHistory.execute (register state).actual.point stages).source.input
  (Financial.accountAt state.actual.point.source.input ordinal)
  (Financial.accountAt (EventHistory.execute (register state).actual.point stages).source.input ordinal) :=
 SuccessorSigningSource.every_future_run_preserves_the_original_financial_prefix
  state.actual.model state.actual.point original stages ordinal bounded

def controlled (control : SourceContinuationTrace.Trace model → LocalCommandSource.Input) : Nat → SourceContinuationTrace.Trace model :=
 Nat.rec (SourceContinuationTrace.initial model saved retained) fun _ trace =>
  SourceContinuationTrace.step model trace (control trace)

theorem every_controlled_prefix_replays_its_actual_source_inputs
 (same : retained=EventStep.seed saved)
 (control : SourceContinuationTrace.Trace model → LocalCommandSource.Input) (count : Nat) :
 SourceContinuationTrace.Sound model saved (controlled model saved retained control count)
  (LocalCommandRun.run model saved (controlled model saved retained control count).inputs) := by
 induction count with
 | zero => exact ⟨rfl,same,rfl,rfl,rfl⟩
 | succ count ih =>
  let prior := controlled model saved retained control count
  have next := SourceContinuationTrace.step_is_the_same_actual_source_step model saved prior _ ih (control prior)
  have replays : LocalCommandRun.run model saved (prior.inputs++[control prior])=
   LocalCommandRun.step model saved (LocalCommandRun.run model saved prior.inputs) (control prior) := by
   simp only [LocalCommandRun.run,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [← replays] at next
  exact next

theorem controlled_keeps_the_source_side
 (control : SourceContinuationTrace.Trace model → LocalCommandSource.Input) (count : Nat) :
 (controlled model saved retained control count).cursor.side=saved.side := by
 induction count with
 | zero => rfl
 | succ count ih => exact ih

theorem original_dynamic_keeps_the_source_side
 (baseline : Nat) (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)) (law : StageReception.Law model.source.code)
 (work : List (Request Party Good Port (Mandate.State Party Technology) Instrument)) (count : Nat) :
 (SourceContinuationTrace.dynamic model saved baseline base law work retained count).cursor.side=saved.side := by
 induction count with
 | zero => rfl
 | succ count ih => exact ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceOpportunityHandoff
