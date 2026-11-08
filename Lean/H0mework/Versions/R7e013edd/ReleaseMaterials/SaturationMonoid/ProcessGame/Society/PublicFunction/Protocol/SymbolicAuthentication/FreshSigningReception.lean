import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningReception
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableCodeLineage

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {old root : Emitter (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument)}
 (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))

-- Capture the global execution itself in the fresh context's Code coordinates.
def parts (global : JointReceptionSource.State old) (lineage : Lineage root global.actual.model.source.code) :
 RenewableArchiveSource.Command → List (RenewableCodeLineage.Row root)
 | .execute inputs => ((RenewableArchiveSource.fresh global.actual inputs).rows global.actual.model).map (pack lineage)
 | .renew enabled accept =>
   (StageTrace.records (PaidInvocationSource.start global.actual.model.source.code contract global.actual.point)
    (PaidInvocationSource.stages global.actual.model.source.code contract enabled accept)).map
    (pack (.extended lineage (PaidInvocationSource.catalogue global.actual.model.source.code contract)))

def lineageAfter (global : JointReceptionSource.State old) (lineage : Lineage root global.actual.model.source.code)
 (command : RenewableArchiveSource.Command) : Lineage root (JointReceptionSource.advance contract global command).actual.model.source.code :=
 match command with
 | .execute _ => lineage
 | .renew _ _ => .extended lineage (PaidInvocationSource.catalogue global.actual.model.source.code contract)

def capture : List RenewableArchiveSource.Command → (global : JointReceptionSource.State old) →
 Lineage root global.actual.model.source.code → List (RenewableCodeLineage.Row root) :=
 List.rec (fun _ _ => []) fun command _tail recur global lineage =>
  parts contract global lineage command++recur (JointReceptionSource.advance contract global command)
   (lineageAfter contract global lineage command)

private theorem the_global_step_is_the_same_actual_record_in_the_new_coordinates
 (global : JointReceptionSource.State old) (localState : JointReceptionSource.State root)
 (lineage : Lineage root global.actual.model.source.code)
 (same : FreshSigningReplay.physical global.actual=FreshSigningReplay.physical localState.actual)
 (sameLineage : HEq lineage localState.lineage) (command : RenewableArchiveSource.Command) :
 parts contract global lineage command=JointReceptionSource.additions contract localState command ∧
 HEq (lineageAfter contract global lineage command) (JointReceptionSource.advance contract localState command).lineage := by
 rcases global with ⟨globalActual,globalLineage,globalRows⟩
 rcases localState with ⟨localActual,localLineage,localRows⟩
 cases globalActual
 cases localActual
 cases same
 cases sameLineage
 cases command <;> exact ⟨rfl,HEq.rfl⟩

theorem captured_global_rows_are_the_same_actual_rows_as_the_local_planning_replay
 (global : JointReceptionSource.State old) (localState : JointReceptionSource.State root)
 (lineage : Lineage root global.actual.model.source.code)
 (same : FreshSigningReplay.physical global.actual=FreshSigningReplay.physical localState.actual)
 (sameLineage : HEq lineage localState.lineage) (commands : List RenewableArchiveSource.Command) :
 localState.rows++capture contract commands global lineage=
 (SourceRepairSearch.execute contract localState commands).rows := by
 induction commands generalizing global localState lineage with
 | nil => exact List.append_nil _
 | cons command tail ih =>
   obtain ⟨records,related⟩ := the_global_step_is_the_same_actual_record_in_the_new_coordinates contract global localState lineage same sameLineage command
   have physical := FreshSigningReplay.the_actual_command_depends_only_on_the_complete_model_and_cursor contract global.actual localState.actual same command
   rw [← JointReceptionSource.advance_is_the_original_actual_command contract global command,
    ← JointReceptionSource.advance_is_the_original_actual_command contract localState command] at physical
   have later := ih (JointReceptionSource.advance contract global command) (JointReceptionSource.advance contract localState command)
    (lineageAfter contract global lineage command) physical related
   change localState.rows++(parts contract global lineage command++capture contract tail
    (JointReceptionSource.advance contract global command) (lineageAfter contract global lineage command))=_
   rw [records,← List.append_assoc,← JointReceptionSource.advance_appends_only_actual_rows]
   exact later

variable (base : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (laws : (model : FreshSigningReplay.Model (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) → StageReception.Law model.source.code)
 (before : JointReceptionSource.State old)
 (request : FreshSigningSource.Request (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def rows : List (RenewableCodeLineage.Row before.actual.model.source.code) :=
 ((FreshSigningSource.origin base laws before request).rows before.actual.model).map (pack Lineage.original)++
 capture (root := before.actual.model.source.code) contract (FreshSigningSource.result contract base laws before request).commands
  (FreshSigningReplay.globalStart contract before (FreshSigningSource.inputs base laws before request)) Lineage.original

theorem fresh_global_rows_equal_the_actual_planner_rows :
 rows contract base laws before request=(FreshSigningSource.result contract base laws before request).final.rows := by
 have same := captured_global_rows_are_the_same_actual_rows_as_the_local_planning_replay contract
  (FreshSigningReplay.globalStart contract before (FreshSigningSource.inputs base laws before request))
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request)) Lineage.original
  (FreshSigningReplay.both_starts_are_the_same_actual_model_and_cursor contract before (FreshSigningSource.inputs base laws before request))
  HEq.rfl (FreshSigningSource.result contract base laws before request).commands
 have replay := (SourceRepairRun.every_report_replays_only_its_selected_actual_source_commands contract
  ((FreshSigningSource.origin base laws before request).vocabulary before.actual.model base)
  ((FreshSigningSource.origin base laws before request).law before.actual.model (laws before.actual.model))
  (FreshSigningSource.origin base laws before request).origin (FreshSigningSource.origin base laws before request).stages
  (FreshSigningReplay.currentScope before request.scope) request.value request.depth
  (SourceRepairSearch.debt ((FreshSigningSource.origin base laws before request).vocabulary before.actual.model base)
    ((FreshSigningSource.origin base laws before request).law before.actual.model (laws before.actual.model))
    (FreshSigningSource.origin base laws before request).origin (FreshSigningSource.origin base laws before request).stages
    (FreshSigningReplay.currentScope before request.scope) request.value
    (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))+1)
  (FreshSigningReplay.localStart before (FreshSigningSource.inputs base laws before request))).1
 exact same.trans (congrArg JointReceptionSource.State.rows replay)

def observed (recipient : Fin before.actual.model.source.code.sites) :=
 RenewableHistoryReception.scan ((FreshSigningSource.origin base laws before request).vocabulary before.actual.model base)
  ((FreshSigningSource.origin base laws before request).law before.actual.model (laws before.actual.model))
  (FreshSigningSource.origin base laws before request).origin (FreshSigningSource.origin base laws before request).stages
  recipient (rows contract base laws before request) 0 ⟨[],[]⟩

theorem the_independent_global_receiver_equals_the_new_context_receiver
 (recipient : Fin before.actual.model.source.code.sites) :
 observed contract base laws before request recipient=
 JointReceptionSource.observed ((FreshSigningSource.origin base laws before request).vocabulary before.actual.model base)
  ((FreshSigningSource.origin base laws before request).law before.actual.model (laws before.actual.model))
  (FreshSigningSource.origin base laws before request).origin (FreshSigningSource.origin base laws before request).stages
  (FreshSigningSource.result contract base laws before request).final recipient := by
 unfold observed JointReceptionSource.observed
 rw [fresh_global_rows_equal_the_actual_planner_rows]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FreshSigningReception
