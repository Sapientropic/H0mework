import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OriginQueue
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CurrentWithdrawalRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedContinuation

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (past : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev current := EventHistory.execute start past
abbrev protocols : Nat → Rule model.source.code := fun _ => SilentWindow.quiet
abbrev horizon := OriginQueue.horizon start (current model start past)
abbrev sweptCursor := OriginQueue.cursorAt start (current model start past) (protocols model) (horizon model start past)
abbrev swept := past ++ OriginQueue.stages start (protocols model) (horizon model start past)

def unhandled := (StageAccountability.ledger start vocabulary encoding law (swept model start past)).filter fun incident =>
  decide (IncidentResponse.identity model start vocabulary encoding law incident ∉
    (IncidentResponse.journal model start (swept model start past) vocabulary encoding law).map
      (IncidentResponse.Answer.id model start vocabulary encoding law))

def alignment := match (unhandled model start past vocabulary encoding law).head? with
  | none => 0
  | some incident => SilentWindow.delay (sweptCursor model start past) incident.receiver

def duration := horizon model start past + alignment model start past vocabulary encoding law

def waiting := if duration model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining then
  past ++ OriginQueue.stages start (protocols model) (duration model start past vocabulary encoding law)
  else past

def responded := if duration model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining then
  IncidentResponse.stages model start (waiting model start past vocabulary encoding law) vocabulary encoding law (OriginQueue.environment start)
  else past

inductive Outcome where
  | exhausted
  | inspected (plan : Option (CurrentWithdrawal.Checked model start (responded model start past vocabulary encoding law) vocabulary encoding law))

def produce : Outcome model start past vocabulary encoding law :=
  if duration model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining then
    .inspected (CurrentWithdrawal.produce model start (responded model start past vocabulary encoding law) vocabulary encoding law)
  else .exhausted

def stages := match produce model start past vocabulary encoding law with
  | .exhausted => past
  | .inspected _ => CurrentWithdrawal.stages model start (responded model start past vocabulary encoding law) vocabulary encoding law (OriginQueue.environment start)

def isPaid : Outcome model start past vocabulary encoding law → Bool
  | .inspected (some entry) => CurrentWithdrawal.isPaid model start (responded model start past vocabulary encoding law) vocabulary encoding law entry
  | _ => false

theorem an_actual_source_selection_resumes_the_original_producer
    (entry : CurrentWithdrawal.Checked model start (responded model start past vocabulary encoding law) vocabulary encoding law)
    (selected : produce model start past vocabulary encoding law = .inspected (some entry)) :
    duration model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining ∧
      CurrentWithdrawal.produce model start (responded model start past vocabulary encoding law) vocabulary encoding law = some entry ∧
      stages model start past vocabulary encoding law =
        CurrentWithdrawal.stages model start (responded model start past vocabulary encoding law) vocabulary encoding law (OriginQueue.environment start) := by
  have step := selected
  unfold produce at step
  split at step
  · exact ⟨by assumption, Outcome.inspected.inj step, by simp only [stages, selected]⟩
  · cases step

theorem the_original_pending_packets_are_attempted_within_the_generated_window
    (enough : duration model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining)
    (serial : Nat) (present : serial < (EventStep.seed (current model start past)).frame.sent.length)
    (pending : serial ∈ QueueScheduler.untried model.source.code (OriginQueue.baseline start)
      (EventStep.seed (current model start past)).past) :
    ∃ index < duration model start past vocabulary encoding law,
      StageReception.delivered (OriginQueue.row start (current model start past) (protocols model) index) serial = true := by
  have fits := (OriginQueue.an_actual_prefix_retains_the_original_baseline start past).length_le
  have bounded : horizon model start past ≤ (EventStep.seed (current model start past)).remaining := by
    unfold duration at enough
    omega
  obtain ⟨index, before, actual⟩ := OriginQueue.the_source_window_generates_an_actual_delivery_attempt
    start (current model start past) (protocols model) fits serial bounded present pending
  change index < horizon model start past at before
  exact ⟨index, by unfold duration; omega, actual⟩

theorem waiting_is_the_actual_source_queue_prefix
    (enough : duration model start past vocabulary encoding law < (EventStep.seed (current model start past)).remaining) :
    EventHistory.execute start (waiting model start past vocabulary encoding law) =
      OriginQueue.cursorAt start (current model start past) (protocols model) (duration model start past vocabulary encoding law) := by
  rw [waiting, if_pos enough, OriginQueue.execute_append, OriginQueue.executed_stages_are_the_actual_cursor]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedContinuation
