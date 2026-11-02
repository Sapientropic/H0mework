import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWindow

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawalRuntime

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
  (ready : IncidentWithdrawal.Ready (model foundation) start past vocabulary encoding law)
  (rival : Opponent (model foundation).source.code)

theorem every_generated_journal_row_is_consumed_by_the_original_root :
    ∀ entry ∈ JournalWithdrawal.inventory (model foundation) start past vocabulary encoding law ready rival
        (tailStages foundation start past protocols vocabulary encoding law ready rival),
      entry ∈ (authority foundation start past protocols vocabulary encoding law scope threshold ready rival).current.challenges := by
  intro entry inside
  rw [(authority foundation start past protocols vocabulary encoding law scope threshold ready rival).current_exact]
  exact JournalWithdrawal.every_generated_row_is_in_the_same_complete_inventory
    (model foundation) start past vocabulary encoding law ready rival
    (tailStages foundation start past protocols vocabulary encoding law ready rival) entry inside

theorem every_original_incident_survives_the_common_attempt
    (answer : IncidentResponse.Answer (model foundation) start vocabulary encoding law)
    (actual : answer ∈ IncidentResponse.journal (model foundation) start past vocabulary encoding law) :
    answer.response.incident ∈ (rooted foundation start past protocols vocabulary encoding law scope threshold ready rival).incidents := by
  have responsePrefix := IncidentResponse.every_answer_retains_its_actual_source_prefix (model foundation) start past vocabulary encoding law answer actual
  have birthPrefix : answer.pastStages <+: past := (List.prefix_append _ _).trans responsePrefix
  obtain ⟨afterResponse, same⟩ := birthPrefix
  have retained : StageAccountability.ledger start vocabulary encoding law answer.pastStages <+:
      StageAccountability.ledger start vocabulary encoding law past := by
    refine ⟨StageAccountability.walk start vocabulary encoding law answer.pastStages afterResponse, ?_⟩
    exact (StageAccountability.ledger_extends_by_its_generated_next start vocabulary encoding law answer.pastStages afterResponse).symm.trans
      (congrArg (StageAccountability.ledger start vocabulary encoding law) same)
  have initial := retained.subset answer.response.actual
  rw [(rooted foundation start past protocols vocabulary encoding law scope threshold ready rival).incidents_exact]
  change answer.response.incident ∈ StageAccountability.ledger start vocabulary encoding law
    ((past ++ [(IncidentWithdrawal.protocol (model foundation) start past vocabulary encoding law ready, rival)]) ++
      tailStages foundation start past protocols vocabulary encoding law ready rival)
  rw [StageAccountability.ledger_extends_by_its_generated_next, StageAccountability.ledger_extends_by_its_generated_next]
  exact List.mem_append_left _ (List.mem_append_left _ initial)

theorem the_same_paid_attempt_settles_the_entire_compatible_journal_with_ledger_and_next
    (accepted : (model foundation).source.code.law.Valid
      (EventStep.seed (IncidentWithdrawal.current (model foundation) start past)).current
      (IncidentWithdrawal.action (model foundation) start past vocabulary encoding law ready.answer))
    (selected : IncidentWithdrawal.produce (model foundation) start past vocabulary encoding law = .paid ready accepted) :
    IncidentWithdrawal.stages (model foundation) start past vocabulary encoding law rival =
      execution foundation start past vocabulary encoding law ready rival ∧
    (∀ (answer : IncidentResponse.Answer (model foundation) start vocabulary encoding law)
        (actual : answer ∈ IncidentResponse.journal (model foundation) start past vocabulary encoding law),
      (JournalWithdrawal.targetReady (model foundation) start past vocabulary encoding law ready rival
          (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual = true →
        (JournalWithdrawal.history (model foundation) start past vocabulary encoding law ready rival
          (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual).isPending _ _ = false) ∧
      (JournalWithdrawal.compatible (model foundation) start past vocabulary encoding law ready answer = true →
        (JournalWithdrawal.history (model foundation) start past vocabulary encoding law ready rival
          (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual).isPending _ _ = false) ∧
      (JournalWithdrawal.compatible (model foundation) start past vocabulary encoding law ready answer = false →
        Mandate.Challenge.readAttempt (family foundation start past protocols vocabulary encoding law ready rival)
          (sourceIndex foundation start past protocols vocabulary encoding law ready rival)
          (JournalWithdrawal.claim (model foundation) start past vocabulary encoding law ready rival
            (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual)
          (attemptPosition foundation start past protocols vocabulary encoding law ready rival) = none) ∧
      answer.response.incident ∈ (rooted foundation start past protocols vocabulary encoding law scope threshold ready rival).incidents) ∧
    (∀ entry ∈ JournalWithdrawal.inventory (model foundation) start past vocabulary encoding law ready rival
        (tailStages foundation start past protocols vocabulary encoding law ready rival),
      entry ∈ (authority foundation start past protocols vocabulary encoding law scope threshold ready rival).current.challenges) ∧
    HEq ((StageAccountabilityRuntime.facade foundation start (execution foundation start past vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt
      (runtime foundation start past protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities))))))
      ((runtime foundation start past protocols vocabulary encoding law scope threshold ready rival).tick.generated.projectionOutcome
        (.inherited (.inherited (.inherited (.inherited (.inherited (.component ()))))))) ∧
    HEq (runtime foundation start past protocols vocabulary encoding law scope threshold ready rival).tick.generated.wholeLedgerWriteBack
      ((runtime foundation start past protocols vocabulary encoding law scope threshold ready rival).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtime foundation start past protocols vocabulary encoding law scope threshold ready rival).current.visit.current) ∧
    (runtime foundation start past protocols vocabulary encoding law scope threshold ready rival).tick.nextCurrent =
      (StageAccountabilityRuntime.facade foundation start (execution foundation start past vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).process.stateAt
        ((StageAccountabilityRuntime.facade foundation start (execution foundation start past vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).process.successor
          (runtime foundation start past protocols vocabulary encoding law scope threshold ready rival).state) := by
  have sameRoot := (StageAccountabilityRuntime.facade foundation start (execution foundation start past vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start past protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities)))))
  refine ⟨execution_is_the_actual_generated_update foundation start past vocabulary encoding law ready rival (Or.inl ⟨accepted, selected⟩), ?_,
    every_generated_journal_row_is_consumed_by_the_original_root foundation start past protocols vocabulary encoding law scope threshold ready rival,
    sameRoot.2.2.2.1, sameRoot.2.2.1, sameRoot.2.2.2.2⟩
  intro answer actual
  exact ⟨JournalWithdrawal.a_common_paid_attempt_closes_every_ready_actual_target (model foundation) start past vocabulary encoding law ready rival
      (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual accepted,
    JournalWithdrawal.a_common_paid_attempt_archives_every_compatible_answer (model foundation) start past vocabulary encoding law ready rival
      (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual accepted,
    JournalWithdrawal.an_incompatible_snapshot_cannot_use_the_common_attempt (model foundation) start past vocabulary encoding law ready rival
      (tailStages foundation start past protocols vocabulary encoding law ready rival) answer actual,
    every_original_incident_survives_the_common_attempt foundation start past protocols vocabulary encoding law scope threshold ready rival answer actual⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.JournalWithdrawalRuntime
