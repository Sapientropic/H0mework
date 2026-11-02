import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Iteration.Input

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.CurrentInputContract
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction
open Computation.Search.Segmented.Publication.Learning.Paid
open Owned.PublicTask.Local.Inquiry.Planning
open Input.Challenge.Redress.Shared.Iteration
open TaskSource.Iteration
noncomputable section
variable (state : TaskSource.Iteration.Current) (word : List Action) (made : Current.Incoming.Result state word)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case001 : made.response = Requests.produce ⟨state.ready,state.cursor.pending⟩ word := made.uses_the_actual_receiver
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case002 : Requests.submitted (Current.Incoming.cursor state) word = state.cursor.pending ++ word := rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case003 : made.target.task = made.rebuilt.task.withOriginAt made.rebuilt.target.saved
    (by rw [made.rebuilt_exact];rfl)
    ((FutureOrigin.receiveAfter state.origin made.response).advance (fun _ => made.rebuilt.native)) := made.keeps_the_same_rebuilt_task
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case004 : made.response.rawOrigins.map (fun origin => origin.item.request) = made.target.cursor.pending := by
  change _ = made.rebuilt.target.pending
  rw [made.rebuilt_exact]
  exact made.response.unresolved_requests_keep_their_original_raw_refusal_positions
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case005 : made.target.task.worldInput.map TaskInput.packet = some made.target.ready := made.target.input
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case006 : made.target.task.worldPending = made.target.cursor.pending := made.target.pending
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case007 : state.task.futureRequests ++ [word] <+: made.target.task.futureRequests := made.every_received_word_is_registered
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case008 : made.target.task.quote = state.task.quote := made.reconstruction_does_not_increase_the_declared_payment.1
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case009 : Input.Event.Evolution state.cursor.saved made.target.cursor.saved := made.native
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case010 : Input.Event.Funding.Receipt made.native := made.funding
variable (round : Current.Incoming.Round state word)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case011 : round.step.original = GlobalPolicy.produce round.received.target.task := round.uses_the_original_planner_at_the_actual_received_task
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case012 : state.task.futureRequests ++ [word] <+: round.target.task.futureRequests := round.keeps_all_old_and_the_actual_new_request
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case013 : Input.Event.Evolution state.cursor.saved round.target.cursor.saved := round.native
variable (words : List (List Action)) (run : Current.Incoming.Run state words)
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case014 : state.task.futureRequests <+: run.finish.task.futureRequests := run.keeps_the_complete_old_directory
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case015 (member : word ∈ words) : word ∈ run.finish.task.futureRequests := run.every_received_word_remains_in_the_final_task word member
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case016 : Input.Event.Evolution state.cursor.saved run.finish.cursor.saved := run.native
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case017 : Input.Event.Funding.Receipt run.native := run.funding
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case018 (bearer : Bool) (good : Good) :
    Input.Event.Funding.account run.native true bearer good + Input.Event.Funding.account run.native false bearer good =
      Input.Event.FinancialBalance.quotedNet state.cursor.saved bearer good -
      Input.Event.FinancialBalance.quotedNet run.finish.cursor.saved bearer good :=
  Input.Event.Funding.actual_net_position_change run.native bearer good
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case019 (row : Input.Event.Future.Expiry.Progress.Responsibility.Row state.cursor.saved) :
    (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).row.origin = row.origin ∧
    row.state.history <+: (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state.history ∧
    Nonempty ((Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).native.Run row.origin.initial
      (Input.Event.Future.Expiry.Progress.Responsibility.transport run.native row).state) :=
  run.every_original_responsibility_keeps_its_actual_history row
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R6c245933.ReleaseMaterials.Scripts.Verification.PublicCurrentInputContract.case020 : (Current.Incoming.receive state []).finish = state := rfl
end
#eval IO.println "PUBLIC CURRENT INPUT CONTRACT PASS: 20/20"
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.CurrentInputContract
