import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.DefaultRawReentryContract
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry Owned.PublicTask.Local.Inquiry.Planning
open Input.Challenge.Redress.Shared.Iteration
open TaskSource
noncomputable section

variable (state : Iteration.Current) (made : Refusal.Result state)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case001 : made.nextCurrent.task = made.rebuilt.task.withOptionalOriginAt made.rebuilt.target.saved
    (by rw [made.rebuilt_exact];rfl) (some made.nextOrigin) := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case002 : made.nextCurrent.cursor = made.rebuilt.target := made.current_keeps_the_same_actual_endpoint
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case003 : made.nextCurrent.task.worldInput.map TaskInput.packet = some made.nextCurrent.ready := made.nextCurrent.input
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case004 : made.nextCurrent.task.worldPending = made.nextCurrent.cursor.pending := made.nextCurrent.pending
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case005 : Input.Event.Evolution state.cursor.saved made.nextCurrent.cursor.saved := made.native
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case006 : made.response = Requests.produce (Refusal.beforeCursor state made.fault) (Refusal.word state made.fault) := made.response_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case007 : (Iteration.Current.produce made.nextCurrent).original = GlobalPolicy.produce made.nextCurrent.task :=
  (Iteration.Current.produce made.nextCurrent).generated

variable (step : Iteration.Current.Step state)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case008 : step.original = GlobalPolicy.produce state.task := step.generated
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case009 (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
    (rejected : GlobalPolicy.produce state.task = .rejected row) :
    (Iteration.Current.produce state).recovery = Refusal.produce state := by
  unfold Iteration.Current.produce
  split
  next row generated =>
    split
    next recovered => exact recovered.symm
    next made recovered => exact recovered.symm
  next cache service generated =>
    cases rejected.symm.trans generated
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case010 (found : step.recovery = some made) : step.blocked = false :=
  step.an_actual_recovery_does_not_stop_recursion made found
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case011 (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
    (rejected : step.original = .rejected row) (found : step.recovery = some made) :
    step.target = made.nextCurrent := step.repaired_refusal_uses_its_actual_successor row rejected made found
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case012 (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
    (rejected : step.original = .rejected row) (found : step.recovery = some made) :
    HEq (Iteration.Current.produce step.target).original (GlobalPolicy.produce made.nextCurrent.task) := by
  rw [step.repaired_refusal_uses_its_actual_successor row rejected made found]
  exact heq_of_eq (Iteration.Current.produce made.nextCurrent).generated
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case013 (row : Selection.Rejection state.task.model state.task.domain state.task.original state.task.baseline state.task.baseline)
    (rejected : step.original = .rejected row) (absent : step.recovery = none) :
    step.target.task = state.task ∧ step.blocked = true := step.an_unrepaired_refusal_keeps_the_original_task row rejected absent
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case014 {cache : Frame state.task} (service : GlobalPolicy.Service state.task cache)
    (selected : step.original = .generated cache service) :
    step.target = Iteration.Current.after state service ∧ step.blocked = false :=
  step.original_services_keep_their_actual_successor service selected

variable {count : Nat} (run : Iteration.Current.Run made.nextCurrent count)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case015 : Input.Event.Evolution state.cursor.saved run.finishCurrent.cursor.saved := .append made.native run.native
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case016 (bearer : Bool) (good : Good) :
    Input.Event.Funding.account (.append made.native run.native) true bearer good +
      Input.Event.Funding.account (.append made.native run.native) false bearer good =
    Input.Event.FinancialBalance.quotedNet state.cursor.saved bearer good -
      Input.Event.FinancialBalance.quotedNet run.finishCurrent.cursor.saved bearer good :=
  Input.Event.Funding.actual_net_position_change (.append made.native run.native) bearer good
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case017 (row : Input.Event.Future.Expiry.Progress.Responsibility.Row state.cursor.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport (.append made.native run.native) row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport (.append made.native run.native) row).state.history :=
  Input.Event.Future.Expiry.Progress.Responsibility.every_actual_step_retains_its_original_admission_and_history (.append made.native run.native) row
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicDefaultRawReentryContract.case018 (raw : Requests.Cursor) : (Iteration.execute 0 raw).finish = raw := rfl

end
#eval IO.println "PUBLIC DEFAULT RAW REENTRY CONTRACT PASS: 18/18"
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.DefaultRawReentryContract
