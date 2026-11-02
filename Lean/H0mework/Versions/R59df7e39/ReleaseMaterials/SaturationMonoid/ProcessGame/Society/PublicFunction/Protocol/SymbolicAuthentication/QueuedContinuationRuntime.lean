import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedContinuation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedContinuationRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation IncidentWithdrawalRuntime

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (model foundation).source.code)
  (past : List (EventHistory.Stage (code := (model foundation).source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (model foundation).source.code)) (law : StageReception.Law (model foundation).source.code)

abbrev resumed := QueuedContinuation.responded (model foundation) start past vocabulary encoding law

structure Selected where
  candidate : CurrentWithdrawal.Candidate (model foundation) start (resumed foundation start past vocabulary encoding law) vocabulary encoding law
  ready : IncidentWithdrawal.Ready (model foundation) start
    (CurrentWithdrawal.waiting (model foundation) start (resumed foundation start past vocabulary encoding law) vocabulary encoding law candidate.val) vocabulary encoding law
  accepted : (model foundation).source.code.law.Valid
    (EventStep.seed (EventHistory.execute start (CurrentWithdrawal.waiting (model foundation) start
      (resumed foundation start past vocabulary encoding law) vocabulary encoding law candidate.val))).current
    (IncidentWithdrawal.action (model foundation) start (CurrentWithdrawal.waiting (model foundation) start
      (resumed foundation start past vocabulary encoding law) vocabulary encoding law candidate.val) vocabulary encoding law ready.answer)
  chosen : QueuedContinuation.produce (model foundation) start past vocabulary encoding law = .inspected (some ⟨candidate, .paid ready accepted⟩)

-- The dependent fields come from the actual producer branch, rather than separate witnesses.
def extract (paid : QueuedContinuation.isPaid (model foundation) start past vocabulary encoding law
    (QueuedContinuation.produce (model foundation) start past vocabulary encoding law) = true) :
    Selected foundation start past vocabulary encoding law := by
  generalize chosen : QueuedContinuation.produce (model foundation) start past vocabulary encoding law = outcome at paid
  cases outcome with
  | exhausted => cases paid
  | inspected result =>
    cases result with
    | none => cases paid
    | some entry =>
      rcases entry with ⟨candidate, plan⟩
      cases plan with
      | paid ready accepted => exact ⟨candidate, ready, accepted, chosen⟩
      | noResponse => cases paid
      | blocked reason => cases paid
      | refused ready denied => cases paid

variable (protocols : Nat → Rule (model foundation).source.code) (scope : Scope) (threshold : Nat)
  (ready : IncidentWithdrawal.Ready (model foundation) start past vocabulary encoding law)
  (rival : Opponent (model foundation).source.code)

theorem every_duty_in_the_same_root_requires_its_actual_content_receipt :
    ∀ row ∈ (rooted foundation start past protocols vocabulary encoding law scope threshold ready rival).source.duties,
      (row.2.2.state.TerminalAt 0 ↔
        ∃ receipt ∈ ((rooted foundation start past protocols vocabulary encoding law scope threshold ready rival).source.source.source.receivers row.1.wire.recipient).receipts,
          receipt.wire.ballot = row.1.wire.ballot) := by
  intro row actual
  have rows : row ∈ StageDuty.histories start vocabulary encoding law
      (StageAccountabilityRuntime.full foundation start (execution foundation start past vocabulary encoding law ready rival) protocols) := actual
  exact StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law _ row rows

omit ready rival in
abbrev consume (selected : Selected foundation start past vocabulary encoding law) :=
  let arrived := CurrentWithdrawal.waiting (model foundation) start (resumed foundation start past vocabulary encoding law)
    vocabulary encoding law selected.candidate.val
  let source := QueuedContinuation.an_actual_source_selection_resumes_the_original_producer (model foundation) start past vocabulary encoding law
    ⟨selected.candidate, .paid selected.ready selected.accepted⟩ selected.chosen
  let original := CurrentWithdrawalRuntime.the_selected_current_response_consumes_the_entire_journal_with_ledger_and_next
    foundation start (resumed foundation start past vocabulary encoding law) protocols vocabulary encoding law scope threshold
    selected.candidate selected.ready (OriginQueue.environment start) selected.accepted source.2.1
  let duties := (StageAccountabilityRuntime.facade foundation start
    (execution foundation start arrived vocabulary encoding law selected.ready (OriginQueue.environment start)) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start arrived protocols vocabulary encoding law scope threshold selected.ready (OriginQueue.environment start)) (.previous .duties)
  And.intro (source.2.2.trans original.1) (And.intro original (And.intro
    (every_duty_in_the_same_root_requires_its_actual_content_receipt foundation start arrived vocabulary encoding law
      protocols scope threshold selected.ready (OriginQueue.environment start)) duties.2.2.2.1))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QueuedContinuationRuntime
