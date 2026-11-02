import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WithdrawalHistory
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawalRuntime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentCompletion

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open IncidentWithdrawalNative

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (pastStages : List (EventHistory.Stage (code := model.source.code)))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (ready : IncidentWithdrawal.Ready model start pastStages vocabulary encoding law)
  (rival : Opponent model.source.code) (more : List (EventHistory.Stage (code := model.source.code)))

theorem every_actual_paid_attempt_archives_the_original_complete_history
    (accepted : model.source.code.law.Valid
      (EventStep.seed (IncidentWithdrawal.current model start pastStages)).current
      (IncidentWithdrawal.action model start pastStages vocabulary encoding law ready.answer)) :
    ∃ claim : Native.Authority.Challenge (native model start pastStages vocabulary encoding law ready rival more),
      claim.position = birthPosition model start pastStages vocabulary encoding law ready rival more ∧
      claim.snapshot (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more) =
          IncidentWithdrawal.snapshot model start vocabulary encoding law ready.answer ∧
      (⟨claim, Mandate.Challenge.through (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim
        (depth model start pastStages vocabulary encoding law ready rival more + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native model start pastStages vocabulary encoding law ready rival more) original) ∈
            (Native.Authority.fullGenerate (native model start pastStages vocabulary encoding law ready rival more)
              (depth model start pastStages vocabulary encoding law ready rival more)).challenges ∧
      (Mandate.Challenge.through (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim
        (depth model start pastStages vocabulary encoding law ready rival more + 2)).isPending _ _ = false := by
  obtain ⟨claim, _, position, snapshot, installed, _⟩ :=
    the_actual_response_generates_its_own_claim_and_attempt model start pastStages vocabulary encoding law ready rival more
  have birthActual := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source start
    (full model start pastStages vocabulary encoding law ready rival more)
    (birthRow model start pastStages vocabulary encoding law ready)
    (birth_is_in_the_same_final_source model start pastStages vocabulary encoding law ready rival more)
  have attemptActual := StageTrace.every_record_is_a_completed_occurrence_of_the_final_source start
    (full model start pastStages vocabulary encoding law ready rival more)
    (attemptRow model start pastStages vocabulary encoding law ready rival)
    (attempt_is_in_the_same_final_source model start pastStages vocabulary encoding law ready rival more)
  have birthCurrent : MandateEvolution.currentAt model.base model.scope
      (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more)
      (birthPosition model start pastStages vocabulary encoding law ready rival more).ordinal =
        (birthRow model start pastStages vocabulary encoding law ready).before.current := birthActual.1.symm
  have attemptCurrent : MandateEvolution.currentAt model.base model.scope
      (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more)
      (attemptPosition model start pastStages vocabulary encoding law ready rival more).ordinal =
        (attemptRow model start pastStages vocabulary encoding law ready rival).before.current := attemptActual.1.symm
  have birth : (MandateEvolution.currentAt model.base model.scope
      (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim.position.ordinal).technology = claim.snapshot _ _ := by
    rw [position, birthCurrent, snapshot]
    rfl
  have same : (MandateEvolution.currentAt model.base model.scope
      (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim.position.ordinal).technology =
      (MandateEvolution.currentAt model.base model.scope
        (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more)
        (attemptPosition model start pastStages vocabulary encoding law ready rival more).ordinal).technology := by
    rw [position, birthCurrent, attemptCurrent]
    exact ready.sameSnapshot.symm
  have single := IncidentChallenge.actual_trace_items model start
    (full model start pastStages vocabulary encoding law ready rival more)
    (attemptRow model start pastStages vocabulary encoding law ready rival)
    (attempt_is_in_the_same_final_source model start pastStages vocabulary encoding law ready rival more)
  have singleton := WithdrawalHistory.a_single_item_visit_has_its_unique_actual_position
    (family model start pastStages vocabulary encoding law ready rival more)
    (sourceIndex model start pastStages vocabulary encoding law ready rival more)
    (attemptPosition model start pastStages vocabulary encoding law ready rival more)
    ((congrArg List.length single).trans (by rw [attempt_items_are_original]; rfl))
  have edge : ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).before.technology =
      (MandateEvolution.currentAt model.base model.scope
        (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more)
        (attemptPosition model start pastStages vocabulary encoding law ready rival more).ordinal).technology := by
    rw [attempt_position_item_is_original, attemptCurrent]
    rfl
  have withdrawal : Mandate.Challenge.Withdrawal (scope := model.scope)
      ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).before
      ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).request := by
    rw [attempt_position_item_is_original]
    exact IncidentWithdrawal.request_has_actual_withdrawal_standing _ _ _ _ _ _ ready
  have valid : (Mandate.law model.base model.scope).Valid
      ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).before
      ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).request := by
    rw [attempt_position_item_is_original, ← model.law_exact]
    exact accepted
  refine ⟨claim, position, snapshot, installed, ?_⟩
  apply WithdrawalHistory.an_actual_paid_withdrawal_closes_the_complete_native_history
    (family model start pastStages vocabulary encoding law ready rival more)
    (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim
    (attemptPosition model start pastStages vocabulary encoding law ready rival more)
    (by rw [position]; exact original_birth_precedes_the_actual_attempt _ _ _ _ _ _ _ _ _)
    birth same singleton edge withdrawal valid
  exact IncidentChallenge.actual_item_is_before_the_native_inventory model start
    (full model start pastStages vocabulary encoding law ready rival more)
    (attemptRow model start pastStages vocabulary encoding law ready rival)
    (attempt_is_in_the_same_final_source model start pastStages vocabulary encoding law ready rival more)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentCompletion

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentCompletionRuntime

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
  (pastStages : List (EventHistory.Stage (code := (AdmissionRuntime.profile foundation).source.code)))
  (protocols : Nat → Rule (AdmissionRuntime.profile foundation).source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)
  (ready : IncidentWithdrawal.Ready (AdmissionRuntime.profile foundation) start pastStages vocabulary encoding law)
  (rival : Opponent (AdmissionRuntime.profile foundation).source.code)
  (accepted : (AdmissionRuntime.profile foundation).source.code.law.Valid
    (EventStep.seed (IncidentWithdrawal.current (AdmissionRuntime.profile foundation) start pastStages)).current
    (IncidentWithdrawal.action (AdmissionRuntime.profile foundation) start pastStages vocabulary encoding law ready.answer))
  (selected : IncidentWithdrawal.produce (AdmissionRuntime.profile foundation) start pastStages vocabulary encoding law = .paid ready accepted)

include selected in
theorem the_original_root_consumes_the_complete_terminal_history :
    IncidentWithdrawal.stages (model foundation) start pastStages vocabulary encoding law rival = execution foundation start pastStages vocabulary encoding law ready rival ∧
    ∃ claim : Native.Authority.Challenge (native foundation start pastStages protocols vocabulary encoding law ready rival),
      claim.position = birthPosition foundation start pastStages protocols vocabulary encoding law ready rival ∧
      (⟨claim, Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law ready rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) claim
        (depth foundation start pastStages protocols vocabulary encoding law ready rival + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native foundation start pastStages protocols vocabulary encoding law ready rival) original) ∈
            (authority foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).current.challenges ∧
      (Mandate.Challenge.through (family foundation start pastStages protocols vocabulary encoding law ready rival)
        (sourceIndex foundation start pastStages protocols vocabulary encoding law ready rival) claim
        (depth foundation start pastStages protocols vocabulary encoding law ready rival + 2)).isPending _ _ = false ∧
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
  obtain ⟨claim, position, _, installed, terminal⟩ :=
    IncidentCompletion.every_actual_paid_attempt_archives_the_original_complete_history
      (model foundation) start pastStages vocabulary encoding law ready rival
      (tailStages foundation start pastStages protocols vocabulary encoding law ready rival) accepted
  have rooted := (StageAccountabilityRuntime.facade foundation start (execution foundation start pastStages vocabulary encoding law ready rival) protocols vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime foundation start pastStages protocols vocabulary encoding law scope threshold ready rival) (.previous (.previous (.previous (.previous (.previous .responsibilities)))))
  refine ⟨execution_is_the_actual_generated_update foundation start pastStages vocabulary encoding law ready rival (Or.inl ⟨accepted, selected⟩),
    claim, position, ?_, terminal,
    the_original_incident_survives_the_actual_attempt foundation start pastStages protocols vocabulary encoding law scope threshold ready rival,
    rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩
  rw [(authority foundation start pastStages protocols vocabulary encoding law scope threshold ready rival).current_exact]
  exact installed

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentCompletionRuntime
