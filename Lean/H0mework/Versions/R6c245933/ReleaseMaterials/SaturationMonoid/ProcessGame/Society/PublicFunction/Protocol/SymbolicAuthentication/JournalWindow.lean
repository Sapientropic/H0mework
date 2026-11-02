import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWindow

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

structure Row where
  response : IncidentResponse.Identity model
  birth : Nat
  compatible : Bool
  targetReady : Bool
  pending : Bool

inductive Outcome where
  | noResponse
  | blocked (reason : IncidentWithdrawal.Obstruction)
  | attempted (paid : Bool) (rows : List (Row model))

abbrev waiting := WithdrawalWindow.waiting model start past vocabulary encoding law

def rows (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law)
    (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code))) : List (Row model) :=
  (IncidentResponse.journal model start (waiting model start past vocabulary encoding law) vocabulary encoding law).attach.map fun original =>
    ⟨IncidentResponse.Answer.id model start vocabulary encoding law original.val,
      (JournalWithdrawal.claim model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more original.val original.property).position.ordinal,
      JournalWithdrawal.compatible model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready original.val,
      JournalWithdrawal.targetReady model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more original.val original.property,
      (JournalWithdrawal.history model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more original.val original.property).isPending _ _⟩

def produce (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code))) : Outcome model :=
  match WithdrawalWindow.produce model start past vocabulary encoding law with
  | .noResponse => .noResponse
  | .blocked reason => .blocked reason
  | .paid ready _ => .attempted true (rows model start past vocabulary encoding law ready rival more)
  | .refused ready _ => .attempted false (rows model start past vocabulary encoding law ready rival more)

theorem every_attempt_retains_the_entire_response_journal
    (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law)
    (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code))) :
    (rows model start past vocabulary encoding law ready rival more).length =
      (IncidentResponse.journal model start (waiting model start past vocabulary encoding law) vocabulary encoding law).length := by
  simp only [rows, List.length_map, List.length_attach]

theorem a_paid_window_completes_every_compatible_row
    (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law)
    (accepted : model.source.code.law.Valid
      (EventStep.seed (WithdrawalWindow.arrival model start past vocabulary encoding law)).current
      (IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready.answer))
    (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code))) :
    ∀ row ∈ rows model start past vocabulary encoding law ready rival more, row.compatible = true → row.pending = false := by
  intro row inside compatible
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp inside
  exact JournalWithdrawal.a_common_paid_attempt_archives_every_compatible_answer model start
    (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more original.val original.property accepted compatible

theorem a_paid_window_completes_every_ready_actual_target
    (ready : IncidentWithdrawal.Ready model start (waiting model start past vocabulary encoding law) vocabulary encoding law)
    (accepted : model.source.code.law.Valid
      (EventStep.seed (WithdrawalWindow.arrival model start past vocabulary encoding law)).current
      (IncidentWithdrawal.action model start (waiting model start past vocabulary encoding law) vocabulary encoding law ready.answer))
    (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code))) :
    ∀ row ∈ rows model start past vocabulary encoding law ready rival more, row.targetReady = true → row.pending = false := by
  intro row inside available
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp inside
  exact JournalWithdrawal.a_common_paid_attempt_closes_every_ready_actual_target model start
    (waiting model start past vocabulary encoding law) vocabulary encoding law ready rival more original.val original.property accepted available

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWindow
