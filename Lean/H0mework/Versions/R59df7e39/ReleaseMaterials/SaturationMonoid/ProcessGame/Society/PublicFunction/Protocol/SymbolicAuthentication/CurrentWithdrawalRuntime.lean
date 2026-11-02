import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CurrentWithdrawal
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawalRuntime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CurrentWithdrawalRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation IncidentWithdrawalRuntime

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (past : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (protocols : Nat → Rule (AdmissionRuntime.profile foundation).source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)
  (candidate : CurrentWithdrawal.Candidate (model foundation) start past vocabulary encoding law)

variable (ready : IncidentWithdrawal.Ready (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law)
  (rival : Opponent (model foundation).source.code)

theorem the_selected_current_response_consumes_the_entire_journal_with_ledger_and_next
    (accepted : (model foundation).source.code.law.Valid
      (EventStep.seed (IncidentWithdrawal.current (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val))).current
      (IncidentWithdrawal.action (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready.answer))
    (selected : CurrentWithdrawal.produce (model foundation) start past vocabulary encoding law = some ⟨candidate, .paid ready accepted⟩) :
    CurrentWithdrawal.stages (model foundation) start past vocabulary encoding law rival =
      execution foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival ∧
    (∀ (answer : IncidentResponse.Answer (model foundation) start vocabulary encoding law)
        (actual : answer ∈ IncidentResponse.journal (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law),
      (JournalWithdrawal.targetReady (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
          (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual = true →
        (JournalWithdrawal.history (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
          (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual).isPending _ _ = false) ∧
      (JournalWithdrawal.compatible (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready answer = true →
        (JournalWithdrawal.history (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
          (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual).isPending _ _ = false) ∧
      (JournalWithdrawal.compatible (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready answer = false →
        Mandate.Challenge.readAttempt (family foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival)
          (sourceIndex foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival)
          (JournalWithdrawal.claim (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
            (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual)
          (attemptPosition foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) = none) ∧
      answer.response.incident ∈ (rooted foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).incidents) ∧
    (∀ entry ∈ JournalWithdrawal.inventory (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
        (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival),
      entry ∈ (authority foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).current.challenges) ∧
    HEq ((StageAccountabilityRuntime.facade foundation start (execution foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt
      (runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities))))))
      ((runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).tick.generated.projectionOutcome
        (.inherited (.inherited (.inherited (.inherited (.inherited (.component ()))))))) ∧
    HEq (runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).tick.generated.wholeLedgerWriteBack
      ((runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).current.visit.current) ∧
    (runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).tick.nextCurrent =
      (StageAccountabilityRuntime.facade foundation start (execution foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).process.stateAt
        ((StageAccountabilityRuntime.facade foundation start (execution foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).process.successor
          (runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival).state) := by
  have sameRoot := (StageAccountabilityRuntime.facade foundation start (execution foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities)))))
  refine ⟨CurrentWithdrawal.paid_appends_the_selected_actual_attempt (model foundation) start past vocabulary encoding law candidate ready rival accepted selected, ?_,
    JournalWithdrawalRuntime.every_generated_journal_row_is_consumed_by_the_original_root foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival,
    sameRoot.2.2.2.1, sameRoot.2.2.1, sameRoot.2.2.2.2⟩
  intro answer actual
  exact ⟨JournalWithdrawal.a_common_paid_attempt_closes_every_ready_actual_target (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
      (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual accepted,
    JournalWithdrawal.a_common_paid_attempt_archives_every_compatible_answer (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
      (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual accepted,
    JournalWithdrawal.an_incompatible_snapshot_cannot_use_the_common_attempt (model foundation) start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) vocabulary encoding law ready rival
      (tailStages foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law ready rival) answer actual,
    JournalWithdrawalRuntime.every_original_incident_survives_the_common_attempt foundation start (CurrentWithdrawal.waiting (model foundation) start past vocabulary encoding law candidate.val) protocols vocabulary encoding law scope threshold ready rival answer actual⟩


end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CurrentWithdrawalRuntime
