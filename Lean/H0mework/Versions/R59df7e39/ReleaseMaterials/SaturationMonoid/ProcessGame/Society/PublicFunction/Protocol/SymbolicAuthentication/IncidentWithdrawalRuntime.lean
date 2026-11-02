import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawalNative

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawalRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (pastStages : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (protocols : Nat → Rule (AdmissionRuntime.profile foundation).source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)
  (ready : IncidentWithdrawal.Ready (AdmissionRuntime.profile foundation) start pastStages vocabulary encoding law)
  (rival : Opponent (AdmissionRuntime.profile foundation).source.code)

abbrev model := AdmissionRuntime.profile foundation
abbrev execution := pastStages ++ [(IncidentWithdrawal.protocol (model foundation) start pastStages vocabulary encoding law ready, rival)]
abbrev tailStages := StageQueue.stages (EventHistory.execute start (execution foundation start pastStages vocabulary encoding law ready rival)) protocols
  (StageQueue.horizon (EventHistory.execute start (execution foundation start pastStages vocabulary encoding law ready rival)))
abbrev native := IncidentWithdrawalNative.native (model foundation) start pastStages vocabulary encoding law ready rival
  (tailStages foundation start pastStages protocols vocabulary encoding law ready rival)
abbrev family := Native.Authority.programme (native foundation start pastStages protocols vocabulary encoding law ready rival)
abbrev sourceIndex := Native.Authority.sourceIndex (native foundation start pastStages protocols vocabulary encoding law ready rival)
abbrev depth := IncidentWithdrawalNative.depth (model foundation) start pastStages vocabulary encoding law ready rival
  (tailStages foundation start pastStages protocols vocabulary encoding law ready rival)
abbrev birthPosition := IncidentWithdrawalNative.birthPosition (model foundation) start pastStages vocabulary encoding law ready rival
  (tailStages foundation start pastStages protocols vocabulary encoding law ready rival)
abbrev attemptPosition := IncidentWithdrawalNative.attemptPosition (model foundation) start pastStages vocabulary encoding law ready rival
  (tailStages foundation start pastStages protocols vocabulary encoding law ready rival)
abbrev rooted := StageAccountabilityRuntime.rooted foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold
abbrev runtime := StageAccountabilityRuntime.activated foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold
  (StageAccountabilityRuntime.ordinal foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols)
abbrev authority := StageAccountabilityRuntime.authority foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold

variable (selected :
  (∃ accepted, IncidentWithdrawal.produce (model foundation) start pastStages vocabulary encoding law = .paid ready accepted) ∨
  (∃ denied, IncidentWithdrawal.produce (model foundation) start pastStages vocabulary encoding law = .refused ready denied))

include selected in
theorem execution_is_the_actual_generated_update :
    IncidentWithdrawal.stages (model foundation) start pastStages vocabulary encoding law rival = execution foundation start pastStages vocabulary encoding law ready rival := by
  rcases selected with ⟨accepted, chosen⟩ | ⟨denied, chosen⟩
  · exact IncidentWithdrawal.paid_appends_the_actual_attempt _ _ _ _ _ _ ready rival accepted chosen
  · exact IncidentWithdrawal.refused_appends_the_actual_attempt _ _ _ _ _ _ ready rival denied chosen

theorem the_original_incident_survives_the_actual_attempt : ready.answer.response.incident ∈
    (rooted foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).incidents := by
  have responsePrefix := IncidentResponse.every_answer_retains_its_actual_source_prefix (model foundation) start pastStages vocabulary encoding law ready.answer ready.actual
  have birthPrefix : ready.answer.pastStages <+: pastStages := (List.prefix_append _ _).trans responsePrefix
  obtain ⟨afterResponse, same⟩ := birthPrefix
  have retained : StageAccountability.ledger start vocabulary encoding law ready.answer.pastStages <+:
      StageAccountability.ledger start vocabulary encoding law pastStages := by
    refine ⟨StageAccountability.walk start vocabulary encoding law ready.answer.pastStages afterResponse, ?_⟩
    exact (StageAccountability.ledger_extends_by_its_generated_next start vocabulary encoding law ready.answer.pastStages afterResponse).symm.trans
      (congrArg (StageAccountability.ledger start vocabulary encoding law) same)
  have initial := retained.subset ready.answer.response.actual
  rw [(rooted foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).incidents_exact]
  change ready.answer.response.incident ∈ StageAccountability.ledger start vocabulary encoding law
    ((pastStages ++ [(IncidentWithdrawal.protocol (model foundation) start pastStages vocabulary encoding law ready, rival)]) ++
      tailStages foundation start pastStages protocols vocabulary encoding law ready rival)
  rw [StageAccountability.ledger_extends_by_its_generated_next, StageAccountability.ledger_extends_by_its_generated_next]
  exact List.mem_append_left _ (List.mem_append_left _ initial)

include selected in
theorem the_original_claim_attempt_and_native_run_are_consumed_by_the_same_root :
    IncidentWithdrawal.stages (model foundation) start pastStages vocabulary encoding law rival = execution foundation start pastStages vocabulary encoding law ready rival ∧
    ∃ claim : Native.Authority.Challenge (native foundation start pastStages protocols vocabulary encoding law ready rival),
      claim.position = birthPosition foundation start pastStages protocols vocabulary encoding law ready rival ∧
      claim.snapshot (family foundation start pastStages protocols vocabulary encoding law ready rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) =
          IncidentWithdrawal.snapshot (model foundation) start vocabulary encoding law ready.answer ∧
      (⟨claim, Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law ready rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) claim
        (depth foundation start pastStages protocols vocabulary encoding law ready rival + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native foundation start pastStages protocols vocabulary encoding law ready rival) original) ∈
            (authority foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).current.challenges ∧
      (∃ attempt, Mandate.Challenge.readAttempt (family foundation start pastStages protocols vocabulary encoding law ready rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) claim
        (attemptPosition foundation start pastStages protocols vocabulary encoding law ready rival) = some attempt) ∧
      (Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law ready rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) claim
        (depth foundation start pastStages protocols vocabulary encoding law ready rival + 2)).state.current.history =
          (Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law ready rival)
            (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) claim
            (depth foundation start pastStages protocols vocabulary encoding law ready rival + 2)).state.generated.events ∧
      ready.answer.response.incident ∈ (rooted foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).incidents ∧
      HEq ((StageAccountabilityRuntime.facade foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt
        (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities))))))
        ((runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).tick.generated.projectionOutcome
          (.inherited (.inherited (.inherited (.inherited (.inherited (.component ()))))))) ∧
      HEq (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).tick.generated.wholeLedgerWriteBack
        ((runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).current.visit.current) ∧
      (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).tick.nextCurrent =
        (StageAccountabilityRuntime.facade foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).process.stateAt
          ((StageAccountabilityRuntime.facade foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).process.successor
            (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).state) := by
  obtain ⟨claim, _, position, snapshot, admitted, attempt⟩ :=
    IncidentWithdrawalNative.the_actual_response_generates_its_own_claim_and_attempt (model foundation) start pastStages vocabulary encoding law ready rival
      (tailStages foundation start pastStages protocols vocabulary encoding law ready rival)
  have installed := (StageAccountabilityRuntime.facade foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities)))))
  refine ⟨execution_is_the_actual_generated_update foundation start pastStages vocabulary encoding law ready rival selected,
    claim, position, snapshot, ?_, attempt, Native.Authority.every_challenge_history_is_its_own_actual_native_run _ claim _,
    the_original_incident_survives_the_actual_attempt foundation start pastStages protocols vocabulary encoding law scope threshold ready rival,
    installed.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩
  rw [(authority foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).current_exact]
  exact admitted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawalRuntime
