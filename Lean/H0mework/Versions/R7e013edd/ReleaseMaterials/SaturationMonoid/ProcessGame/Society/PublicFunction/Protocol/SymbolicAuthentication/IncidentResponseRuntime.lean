import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponseRuntime

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
  (rival : Opponent (AdmissionRuntime.profile foundation).source.code)

abbrev model := AdmissionRuntime.profile foundation
abbrev emitted := IncidentResponse.stages (model foundation) start pastStages vocabulary encoding law rival
abbrev full := StageQueueProgress.completeStages start (emitted foundation start pastStages vocabulary encoding law rival) protocols
abbrev native := IncidentChallenge.native (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
abbrev family := Native.Authority.programme (native foundation start pastStages protocols vocabulary encoding law rival)
abbrev sourceIndex := Native.Authority.sourceIndex (native foundation start pastStages protocols vocabulary encoding law rival)
abbrev depth := IncidentChallenge.depth (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
abbrev rooted := StageAccountabilityRuntime.rooted foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold
abbrev runtime := StageAccountabilityRuntime.activated foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold
  (StageAccountabilityRuntime.ordinal foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols)
abbrev authority := StageAccountabilityRuntime.authority foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold

variable (response : IncidentResponse.Ready (model foundation) start pastStages vocabulary encoding law)
  (selected : IncidentResponse.produce (model foundation) start pastStages vocabulary encoding law = .ready response)

abbrev actualRow := IncidentResponse.row (model foundation) start pastStages vocabulary encoding law response rival
abbrev item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨0, (EventStep.seed (IncidentResponse.current (model foundation) start pastStages)).current,
    IncidentResponse.signature (model foundation) response.incident.receiver⟩

theorem response_items_are_the_original_signature : StageTrace.items (actualRow foundation start pastStages vocabulary encoding law rival response) =
    [item foundation start pastStages vocabulary encoding law response] := by
  unfold StageTrace.items
  rw [IncidentResponse.response_submits_its_original_signature]
  rfl

def itemIndex : Fin (StageTrace.items (actualRow foundation start pastStages vocabulary encoding law rival response)).length :=
  ⟨0, by rw [response_items_are_the_original_signature]; exact Nat.zero_lt_succ 0⟩

theorem response_item_is_original : (StageTrace.items (actualRow foundation start pastStages vocabulary encoding law rival response)).get
    (itemIndex foundation start pastStages vocabulary encoding law rival response) = item foundation start pastStages vocabulary encoding law response := by
  simp only [itemIndex, List.get_eq_getElem, response_items_are_the_original_signature, List.getElem_cons_zero]

include selected in
theorem the_actual_response_is_in_the_same_final_source :
    actualRow foundation start pastStages vocabulary encoding law rival response ∈ StageTrace.records start
      (full foundation start pastStages protocols vocabulary encoding law rival) := by
  have first : actualRow foundation start pastStages vocabulary encoding law rival response ∈ StageTrace.records start
      (emitted foundation start pastStages vocabulary encoding law rival) := by
    unfold emitted
    rw [IncidentResponse.ready_appends_the_actual_response_stage _ _ _ _ _ _ response rival selected, StageQueue.records_append]
    exact List.mem_append_right _ (List.mem_cons_self)
  unfold full StageQueueProgress.completeStages
  rw [StageQueue.records_append]
  exact List.mem_append_left _ first

include selected in
theorem the_original_incident_is_in_the_same_root : response.incident ∈
    (rooted foundation start pastStages protocols vocabulary encoding law scope threshold rival).incidents := by
  have first : StageAccountability.ledger start vocabulary encoding law pastStages <+:
      StageAccountability.ledger start vocabulary encoding law (emitted foundation start pastStages vocabulary encoding law rival) := by
    unfold emitted
    rw [IncidentResponse.ready_appends_the_actual_response_stage _ _ _ _ _ _ response rival selected,
      StageAccountability.ledger_extends_by_its_generated_next]
    exact List.prefix_append _ _
  have later : StageAccountability.ledger start vocabulary encoding law (emitted foundation start pastStages vocabulary encoding law rival) <+:
      StageAccountability.ledger start vocabulary encoding law (full foundation start pastStages protocols vocabulary encoding law rival) := by
    unfold full StageQueueProgress.completeStages
    rw [StageAccountability.ledger_extends_by_its_generated_next]
    exact List.prefix_append _ _
  exact (first.trans later).subset response.actual

include selected in
theorem the_incident_generates_an_actual_native_challenge_in_its_own_root :
    ∃ claim : Native.Authority.Challenge (native foundation start pastStages protocols vocabulary encoding law rival),
      claim.position.ordinal = EventStep.boundary (IncidentResponse.current (model foundation) start pastStages) ∧
      EventStep.boundary (EventHistory.execute start response.incident.pastStages) < claim.position.ordinal ∧
      (⟨claim, Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law rival) claim
        (depth foundation start pastStages protocols vocabulary encoding law rival + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native foundation start pastStages protocols vocabulary encoding law rival) original) ∈
            (authority foundation start pastStages protocols vocabulary encoding law scope threshold rival).current.challenges ∧
      response.incident ∈ (rooted foundation start pastStages protocols vocabulary encoding law scope threshold rival).incidents ∧
      (actualRow foundation start pastStages vocabulary encoding law rival response).submitted =
        [IncidentResponse.signature (model foundation) response.incident.receiver] ∧
      HEq ((StageAccountabilityRuntime.facade foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold).readoutAt
        (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival) (.previous (.previous (.previous (.previous (.previous .responsibilities))))))
        ((runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival).tick.generated.projectionOutcome
          (.inherited (.inherited (.inherited (.inherited (.inherited (.component ()))))))) ∧
      HEq (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival).tick.generated.wholeLedgerWriteBack
        ((runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival).current.visit.current) ∧
      (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival).tick.nextCurrent =
        (StageAccountabilityRuntime.facade foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold).process.stateAt
          ((StageAccountabilityRuntime.facade foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold).process.successor
            (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival).state) := by
  have inside := the_actual_response_is_in_the_same_final_source foundation start pastStages protocols vocabulary encoding law rival response selected
  have original := response_item_is_original foundation start pastStages vocabulary encoding law rival response
  obtain ⟨claim, _, claimPosition, admitted⟩ := IncidentChallenge.actual_signed_active_item_generates_a_native_claim
    (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
    (actualRow foundation start pastStages vocabulary encoding law rival response) inside
    (itemIndex foundation start pastStages vocabulary encoding law rival response)
    (by rw [original]; exact response.standing) (by rw [original]; exact response.valid) (by rw [original]; exact response.active)
  have ordinal : claim.position.ordinal = EventStep.boundary (IncidentResponse.current (model foundation) start pastStages) := by rw [claimPosition]; rfl
  have past : response.incident.birthStages <+: pastStages := by
    simpa only [List.nil_append] using StageAccountability.every_generated_incident_has_its_original_birth_prefix start vocabulary encoding law [] pastStages response.incident response.actual
  have earlier : response.incident.birthStages.length ≤ pastStages.length := by
    obtain ⟨more, same⟩ := past
    have lengths := congrArg List.length same
    simp only [StageAccountability.Incident.birthStages, List.length_append, List.length_singleton] at lengths ⊢
    omega
  have follows : EventStep.boundary (EventHistory.execute start response.incident.pastStages) < claim.position.ordinal := by
    rw [ordinal]
    change EventStep.boundary (EventHistory.execute start response.incident.pastStages) < EventStep.boundary (EventHistory.execute start pastStages)
    rw [IncidentChallenge.execution_advances_the_actual_boundary (model foundation) start response.incident.pastStages,
      IncidentChallenge.execution_advances_the_actual_boundary (model foundation) start pastStages]
    simp only [StageAccountability.Incident.birthStages, List.length_append, List.length_singleton] at earlier
    omega
  have installed := (StageAccountabilityRuntime.facade foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival) (.previous (.previous (.previous (.previous (.previous .responsibilities)))))
  refine ⟨claim, ordinal, follows, ?_, the_original_incident_is_in_the_same_root foundation start pastStages protocols vocabulary encoding law scope threshold rival response selected,
    IncidentResponse.response_submits_its_original_signature _ _ _ _ _ _ response rival,
    installed.2.2.2.1, installed.2.2.1, installed.2.2.2.2⟩
  rw [(authority foundation start pastStages protocols vocabulary encoding law scope threshold rival).current_exact]
  exact admitted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponseRuntime
