import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponseRuntime

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
abbrev emitted := RejectionResponse.stages (model foundation) start pastStages vocabulary encoding law rival
abbrev full := StageQueueProgress.completeStages start (emitted foundation start pastStages vocabulary encoding law rival) protocols
abbrev native := IncidentChallenge.native (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
abbrev family := Native.Authority.programme (native foundation start pastStages protocols vocabulary encoding law rival)
abbrev sourceIndex := Native.Authority.sourceIndex (native foundation start pastStages protocols vocabulary encoding law rival)
abbrev depth := IncidentChallenge.depth (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
abbrev rooted := StageAccountabilityRuntime.rooted foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold
abbrev runtime := StageAccountabilityRuntime.activated foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold
  (StageAccountabilityRuntime.ordinal foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols)
abbrev authority := StageAccountabilityRuntime.authority foundation start (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold

variable (response : RejectionResponse.Ready (model foundation) start pastStages vocabulary encoding law)
  (selected : RejectionResponse.produce (model foundation) start pastStages vocabulary encoding law = .ready response)

abbrev actualRow := RejectionResponse.row (model foundation) start pastStages vocabulary encoding law response rival
abbrev item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨0, (EventStep.seed (RejectionResponse.current (model foundation) start pastStages)).current,
    RejectionResponse.signature (model foundation) response.receiver⟩

theorem response_items_are_the_original_signature : StageTrace.items (actualRow foundation start pastStages vocabulary encoding law rival response) =
    [item foundation start pastStages vocabulary encoding law response] := by
  unfold StageTrace.items
  rw [RejectionResponse.response_submits_its_original_signature]
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
    rw [RejectionResponse.ready_appends_the_actual_response_stage _ _ _ _ _ _ response rival selected, StageQueue.records_append]
    exact List.mem_append_right _ (List.mem_cons_self)
  unfold full StageQueueProgress.completeStages
  rw [StageQueue.records_append]
  exact List.mem_append_left _ first

include selected in
theorem the_original_rejection_is_in_the_same_root :
    (response.evidence.row.cursor.cut, some response.evidence.wire, .rejected response.evidence.reason) ∈
      ((rooted foundation start pastStages protocols vocabulary encoding law scope threshold rival).source.source.source.receivers response.receiver).audit := by
  have initial : pastStages <+: emitted foundation start pastStages vocabulary encoding law rival := by
    unfold emitted
    rw [RejectionResponse.ready_appends_the_actual_response_stage _ _ _ _ _ _ response rival selected]
    exact List.prefix_append _ _
  have later : emitted foundation start pastStages vocabulary encoding law rival <+:
      full foundation start pastStages protocols vocabulary encoding law rival := List.prefix_append _ _
  obtain ⟨more, same⟩ := initial.trans later
  have retained := ReceptionEvidence.the_rejection_survives_actual_extension start pastStages vocabulary encoding law response.receiver response.evidence more
  rw [same] at retained
  exact retained

include selected in
theorem the_rejection_generates_its_actual_native_claim_in_the_original_root :
    ∃ claim : Native.Authority.Challenge (native foundation start pastStages protocols vocabulary encoding law rival),
      IncidentChallenge.read (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
        (actualRow foundation start pastStages vocabulary encoding law rival response)
        (the_actual_response_is_in_the_same_final_source foundation start pastStages protocols vocabulary encoding law rival response selected)
        (itemIndex foundation start pastStages vocabulary encoding law rival response) = some claim ∧
      claim.position.ordinal = EventStep.boundary (RejectionResponse.current (model foundation) start pastStages) ∧
      (⟨claim, Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law rival) claim
        (depth foundation start pastStages protocols vocabulary encoding law rival + 2)⟩ :
        Sigma fun original => Native.Authority.ChallengeHistory (native foundation start pastStages protocols vocabulary encoding law rival) original) ∈
          (authority foundation start pastStages protocols vocabulary encoding law scope threshold rival).current.challenges := by
  have inside := the_actual_response_is_in_the_same_final_source foundation start pastStages protocols vocabulary encoding law rival response selected
  have original := response_item_is_original foundation start pastStages vocabulary encoding law rival response
  obtain ⟨claim, decoded, claimPosition, admitted⟩ := IncidentChallenge.actual_signed_active_item_generates_a_native_claim
    (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival)
    (actualRow foundation start pastStages vocabulary encoding law rival response) inside
    (itemIndex foundation start pastStages vocabulary encoding law rival response)
    (by rw [original]; exact response.standing) (by rw [original]; exact response.valid) (by rw [original]; exact response.active)
  refine ⟨claim, decoded, ?_, ?_⟩
  · rw [claimPosition]; rfl
  · rw [(authority foundation start pastStages protocols vocabulary encoding law scope threshold rival).current_exact]
    exact admitted

theorem every_registered_rejection_response_reaches_the_same_original_root :
    ∀ answer ∈ RejectionResponse.journal (model foundation) start
        (emitted foundation start pastStages vocabulary encoding law rival) vocabulary encoding law,
      ∃ claim : Native.Authority.Challenge (native foundation start pastStages protocols vocabulary encoding law rival),
        claim.position.ordinal = EventStep.boundary (EventHistory.execute start answer.pastStages) ∧
        (⟨claim, Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law rival)
          (sourceIndex foundation start pastStages protocols vocabulary encoding law rival) claim
          (depth foundation start pastStages protocols vocabulary encoding law rival + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native foundation start pastStages protocols vocabulary encoding law rival) original) ∈
            (authority foundation start pastStages protocols vocabulary encoding law scope threshold rival).current.challenges ∧
        (answer.response.evidence.row.cursor.cut, some answer.response.evidence.wire, .rejected answer.response.evidence.reason) ∈
          ((rooted foundation start pastStages protocols vocabulary encoding law scope threshold rival).source.source.source.receivers answer.response.receiver).audit := by
  intro answer actual
  let row := StageTrace.material (EventHistory.execute start answer.pastStages) answer.actualRule answer.rival
  have first := RejectionResponse.every_registered_response_is_an_actual_history_row (model foundation) start
    (emitted foundation start pastStages vocabulary encoding law rival) vocabulary encoding law answer actual
  have inside : row ∈ StageTrace.records start (full foundation start pastStages protocols vocabulary encoding law rival) := by
    unfold full StageQueueProgress.completeStages
    rw [StageQueue.records_append]
    exact List.mem_append_left _ first
  have submitted := (RejectionResponse.every_answer_has_the_actual_owned_signature (model foundation) start vocabulary encoding law answer).2
  have items : StageTrace.items row = [⟨0, (EventStep.seed (EventHistory.execute start answer.pastStages)).current,
      RejectionResponse.signature (model foundation) answer.response.receiver⟩] := by
    unfold StageTrace.items
    rw [submitted]
    rfl
  let index : Fin (StageTrace.items row).length := ⟨0, by rw [items]; exact Nat.zero_lt_succ 0⟩
  have original : (StageTrace.items row).get index =
      ⟨0, (EventStep.seed (EventHistory.execute start answer.pastStages)).current,
        RejectionResponse.signature (model foundation) answer.response.receiver⟩ := by
    simp only [index, List.get_eq_getElem, items, List.getElem_cons_zero]
  obtain ⟨claim, _, position, admitted⟩ := IncidentChallenge.actual_signed_active_item_generates_a_native_claim
    (model foundation) start (full foundation start pastStages protocols vocabulary encoding law rival) row inside index
    (by rw [original]; exact answer.response.standing) (by rw [original]; exact answer.response.valid)
    (by rw [original]; exact answer.response.active)
  have prefixHistory : answer.pastStages <+: full foundation start pastStages protocols vocabulary encoding law rival :=
    (List.prefix_append _ _).trans ((RejectionResponse.every_answer_retains_its_actual_source_prefix (model foundation) start
      (emitted foundation start pastStages vocabulary encoding law rival) vocabulary encoding law answer actual).trans (List.prefix_append _ _))
  obtain ⟨more, same⟩ := prefixHistory
  have audit := ReceptionEvidence.the_rejection_survives_actual_extension start answer.pastStages vocabulary encoding law
    answer.response.receiver answer.response.evidence more
  rw [same] at audit
  refine ⟨claim, ?_, ?_, audit⟩
  · rw [position]; rfl
  · rw [(authority foundation start pastStages protocols vocabulary encoding law scope threshold rival).current_exact]
    exact admitted

theorem every_original_duty_still_requires_its_actual_content_receipt :
    ∀ row ∈ (rooted foundation start pastStages protocols vocabulary encoding law scope threshold rival).source.duties,
      (row.2.2.state.TerminalAt 0 ↔
        ∃ receipt ∈ ((rooted foundation start pastStages protocols vocabulary encoding law scope threshold rival).source.source.source.receivers row.1.wire.recipient).receipts,
          receipt.wire.ballot = row.1.wire.ballot) := by
  intro row actual
  have member : row ∈ StageDuty.histories start vocabulary encoding law
      (full foundation start pastStages protocols vocabulary encoding law rival) := actual
  exact StageDuty.generated_row_terminal_iff_the_actual_receiver_confirms start vocabulary encoding law _ row member

include selected in
abbrev consume :=
  let installed := (StageAccountabilityRuntime.facade foundation start
    (emitted foundation start pastStages vocabulary encoding law rival) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start pastStages protocols vocabulary encoding law scope threshold rival)
    (.previous (.previous (.previous (.previous (.previous .responsibilities)))))
  And.intro (the_original_rejection_is_in_the_same_root foundation start pastStages protocols vocabulary encoding law scope threshold rival response selected)
    (And.intro (the_rejection_generates_its_actual_native_claim_in_the_original_root foundation start pastStages protocols vocabulary encoding law scope threshold rival response selected)
    (And.intro (every_registered_rejection_response_reaches_the_same_original_root foundation start pastStages protocols vocabulary encoding law scope threshold rival)
    (And.intro (every_original_duty_still_requires_its_actual_content_receipt foundation start pastStages protocols vocabulary encoding law scope threshold rival)
    (And.intro (ReceptionEvidence.incoming_is_an_actual_delivery start pastStages vocabulary encoding law response.receiver response.evidence)
    (And.intro (ReceptionEvidence.incoming_has_its_actual_authenticated_origin start pastStages vocabulary encoding law response.receiver response.evidence)
    (And.intro (StageTransport.authenticated_wire_has_actual_send_and_paid_ballot vocabulary encoding start pastStages response.evidence.wire
      (ReceptionEvidence.incoming_has_its_actual_authenticated_origin start pastStages vocabulary encoding law response.receiver response.evidence))
    (And.intro (RejectionResponse.response_submits_its_original_signature (model foundation) start pastStages vocabulary encoding law response rival)
    (And.intro (RejectionResponse.a_ready_response_has_not_been_registered (model foundation) start pastStages vocabulary encoding law response selected)
    (And.intro installed.2.2.2.1 (And.intro installed.2.2.1 installed.2.2.2.2))))))))))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponseRuntime
