import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawalNative

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

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

abbrev full := pastStages ++ [(IncidentWithdrawal.protocol model start pastStages vocabulary encoding law ready, rival)] ++ more
abbrev native := IncidentChallenge.native model start (full model start pastStages vocabulary encoding law ready rival more)
abbrev family := Native.Authority.programme (native model start pastStages vocabulary encoding law ready rival more)
abbrev sourceIndex := Native.Authority.sourceIndex (native model start pastStages vocabulary encoding law ready rival more)
abbrev depth := IncidentChallenge.depth model start (full model start pastStages vocabulary encoding law ready rival more)
abbrev birthRow := StageTrace.material (EventHistory.execute start ready.answer.pastStages) ready.answer.actualRule ready.answer.rival
abbrev attemptRow := IncidentWithdrawal.row model start pastStages vocabulary encoding law ready rival
abbrev birthItem : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨0, (EventStep.seed (EventHistory.execute start ready.answer.pastStages)).current,
    IncidentResponse.signature model ready.answer.response.incident.receiver⟩
abbrev attemptItem : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨0, (EventStep.seed (IncidentWithdrawal.current model start pastStages)).current,
    IncidentWithdrawal.action model start pastStages vocabulary encoding law ready.answer⟩

theorem birth_items_are_original : StageTrace.items (birthRow model start pastStages vocabulary encoding law ready) =
    [birthItem model start pastStages vocabulary encoding law ready] := by
  have actual := (IncidentResponse.every_answer_has_the_actual_owned_signature model start vocabulary encoding law ready.answer).2
  unfold StageTrace.items
  rw [actual]
  rfl

theorem attempt_items_are_original : StageTrace.items (attemptRow model start pastStages vocabulary encoding law ready rival) =
    [attemptItem model start pastStages vocabulary encoding law ready] := by
  unfold StageTrace.items
  rw [IncidentWithdrawal.attempt_submits_the_actual_member_request]
  rfl

def birthIndex : Fin (StageTrace.items (birthRow model start pastStages vocabulary encoding law ready)).length :=
  ⟨0, by rw [birth_items_are_original]; exact Nat.zero_lt_succ 0⟩
def attemptIndex : Fin (StageTrace.items (attemptRow model start pastStages vocabulary encoding law ready rival)).length :=
  ⟨0, by rw [attempt_items_are_original]; exact Nat.zero_lt_succ 0⟩

theorem birth_item_is_original : (StageTrace.items (birthRow model start pastStages vocabulary encoding law ready)).get
    (birthIndex model start pastStages vocabulary encoding law ready) = birthItem model start pastStages vocabulary encoding law ready := by
  simp only [birthIndex, List.get_eq_getElem, birth_items_are_original, List.getElem_cons_zero]
theorem attempt_item_is_original : (StageTrace.items (attemptRow model start pastStages vocabulary encoding law ready rival)).get
    (attemptIndex model start pastStages vocabulary encoding law ready rival) = attemptItem model start pastStages vocabulary encoding law ready := by
  simp only [attemptIndex, List.get_eq_getElem, attempt_items_are_original, List.getElem_cons_zero]

theorem birth_is_in_the_same_final_source : birthRow model start pastStages vocabulary encoding law ready ∈
    StageTrace.records start (full model start pastStages vocabulary encoding law ready rival more) := by
  have inside := IncidentResponse.every_registered_response_is_an_actual_history_row model start pastStages vocabulary encoding law ready.answer ready.actual
  rw [full, StageQueue.records_append, StageQueue.records_append]
  exact List.mem_append_left _ (List.mem_append_left _ inside)

theorem attempt_is_in_the_same_final_source : attemptRow model start pastStages vocabulary encoding law ready rival ∈
    StageTrace.records start (full model start pastStages vocabulary encoding law ready rival more) := by
  rw [full, StageQueue.records_append, StageQueue.records_append]
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

abbrev birthPosition := IncidentChallenge.position model start (full model start pastStages vocabulary encoding law ready rival more)
  (birthRow model start pastStages vocabulary encoding law ready) (birth_is_in_the_same_final_source model start pastStages vocabulary encoding law ready rival more)
  (birthIndex model start pastStages vocabulary encoding law ready)
abbrev attemptPosition := IncidentChallenge.position model start (full model start pastStages vocabulary encoding law ready rival more)
  (attemptRow model start pastStages vocabulary encoding law ready rival) (attempt_is_in_the_same_final_source model start pastStages vocabulary encoding law ready rival more)
  (attemptIndex model start pastStages vocabulary encoding law ready rival)

theorem birth_position_item_is_original : (birthPosition model start pastStages vocabulary encoding law ready rival more).item
    (family model start pastStages vocabulary encoding law ready rival more) (sourceIndex model start pastStages vocabulary encoding law ready rival more) =
      birthItem model start pastStages vocabulary encoding law ready :=
  (IncidentChallenge.position_item_is_the_actual_item _ _ _ _ _ _).trans (birth_item_is_original _ _ _ _ _ _ _)
theorem attempt_position_item_is_original : (attemptPosition model start pastStages vocabulary encoding law ready rival more).item
    (family model start pastStages vocabulary encoding law ready rival more) (sourceIndex model start pastStages vocabulary encoding law ready rival more) =
      attemptItem model start pastStages vocabulary encoding law ready :=
  (IncidentChallenge.position_item_is_the_actual_item _ _ _ _ _ _).trans (attempt_item_is_original _ _ _ _ _ _ _ _)

theorem original_birth_precedes_the_actual_attempt :
    (birthPosition model start pastStages vocabulary encoding law ready rival more).ordinal <
      (attemptPosition model start pastStages vocabulary encoding law ready rival more).ordinal := by
  have prior := IncidentResponse.every_answer_retains_its_actual_source_prefix model start pastStages vocabulary encoding law ready.answer ready.actual
  obtain ⟨tail, same⟩ := prior
  have lengths := congrArg List.length same
  simp only [IncidentResponse.Answer.birthStages, List.length_append, List.length_singleton] at lengths
  change EventStep.boundary (EventHistory.execute start ready.answer.pastStages) < EventStep.boundary (EventHistory.execute start pastStages)
  rw [IncidentChallenge.execution_advances_the_actual_boundary model start ready.answer.pastStages,
    IncidentChallenge.execution_advances_the_actual_boundary model start pastStages]
  omega

theorem the_actual_response_generates_its_own_claim_and_attempt :
    ∃ claim : Native.Authority.Challenge (native model start pastStages vocabulary encoding law ready rival more),
      Mandate.Challenge.read (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more) (birthPosition model start pastStages vocabulary encoding law ready rival more) = some claim ∧
      claim.position = birthPosition model start pastStages vocabulary encoding law ready rival more ∧
      claim.snapshot (family model start pastStages vocabulary encoding law ready rival more) (sourceIndex model start pastStages vocabulary encoding law ready rival more) =
        IncidentWithdrawal.snapshot model start vocabulary encoding law ready.answer ∧
      (⟨claim, Mandate.Challenge.through (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim (depth model start pastStages vocabulary encoding law ready rival more + 2)⟩ :
          Sigma fun original => Native.Authority.ChallengeHistory (native model start pastStages vocabulary encoding law ready rival more) original) ∈
            (Native.Authority.fullGenerate (native model start pastStages vocabulary encoding law ready rival more) (depth model start pastStages vocabulary encoding law ready rival more)).challenges ∧
      ∃ attempt, Mandate.Challenge.readAttempt (family model start pastStages vocabulary encoding law ready rival more)
        (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim (attemptPosition model start pastStages vocabulary encoding law ready rival more) = some attempt := by
  have item := birth_item_is_original model start pastStages vocabulary encoding law ready
  obtain ⟨claim, decoded, position, admitted⟩ := IncidentChallenge.actual_signed_active_item_generates_a_native_claim
    model start (full model start pastStages vocabulary encoding law ready rival more)
    (birthRow model start pastStages vocabulary encoding law ready) (birth_is_in_the_same_final_source _ _ _ _ _ _ _ _ _)
    (birthIndex model start pastStages vocabulary encoding law ready)
    (by rw [item]; exact ready.answer.response.standing) (by rw [item]; exact ready.answer.response.valid)
    (by rw [item]; exact ready.answer.response.active)
  have snapshot : claim.snapshot (family model start pastStages vocabulary encoding law ready rival more) (sourceIndex model start pastStages vocabulary encoding law ready rival more) =
      IncidentWithdrawal.snapshot model start vocabulary encoding law ready.answer := by
    unfold Mandate.Challenge.Claim.snapshot
    rw [position, birth_position_item_is_original]
  have later : Mandate.Challenge.Later (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim.position (attemptPosition model start pastStages vocabulary encoding law ready rival more) := by
    rw [position]
    exact Or.inl (original_birth_precedes_the_actual_attempt _ _ _ _ _ _ _ _ _)
  have signed : Mandate.Challenge.Withdrawal (scope := model.scope)
      ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).before
      ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).request := by
    rw [attempt_position_item_is_original]
    exact IncidentWithdrawal.request_has_actual_withdrawal_standing _ _ _ _ _ _ ready
  have sameSnapshot : ((attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).before.technology = claim.snapshot _ _ := by
    rw [attempt_position_item_is_original, snapshot]
    exact ready.sameSnapshot
  refine ⟨claim, decoded, position, snapshot, admitted, ?_⟩
  unfold Mandate.Challenge.readAttempt
  rw [dif_pos ⟨later, signed, sameSnapshot⟩]
  exact ⟨_, rfl⟩

-- The native lifecycle sees an attempted edge even when resources reject its raw request.
theorem the_actual_attempt_separates_terminal_from_deferred
    (claim : Native.Authority.Challenge (native model start pastStages vocabulary encoding law ready rival more))
    (attempt : Mandate.Challenge.Attempt (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim)
    (decoded : Mandate.Challenge.readAttempt (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim
      (attemptPosition model start pastStages vocabulary encoding law ready rival more) = some attempt) :
    (Mandate.Challenge.History.receive (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more)
      (Mandate.Challenge.History.initial _ _ claim) (attemptPosition model start pastStages vocabulary encoding law ready rival more)).isPending _ _ =
        !decide (model.source.code.law.Valid (attemptItem model start pastStages vocabulary encoding law ready).before
          (attemptItem model start pastStages vocabulary encoding law ready).request) ∧
    (model.source.code.law.Valid (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request →
      (model.source.code.law.step (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request).technology.holder = none ∧
      (model.source.code.law.step (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request).technology.offered = none ∧
      (model.source.code.law.step (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request).technology.version =
          (claim.snapshot (family model start pastStages vocabulary encoding law ready rival more) (sourceIndex model start pastStages vocabulary encoding law ready rival more)).version + 1) ∧
    (¬model.source.code.law.Valid (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request →
      model.source.code.law.step (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request = (attemptItem model start pastStages vocabulary encoding law ready).before) := by
  have attemptPosition : attempt.position = IncidentWithdrawalNative.attemptPosition model start pastStages vocabulary encoding law ready rival more := by
    unfold Mandate.Challenge.readAttempt at decoded
    split at decoded
    · cases Option.some.inj decoded; rfl
    · cases decoded
  have originalItem := attempt_position_item_is_original model start pastStages vocabulary encoding law ready rival more
  have unsigned : ¬Mandate.Challenge.Submission (scope := model.scope)
      ((IncidentWithdrawalNative.attemptPosition model start pastStages vocabulary encoding law ready rival more).item _ _).request := by
    rw [originalItem]
    simp [Mandate.Challenge.Submission, IncidentWithdrawal.action, Mandate.request]
  have noClaim : Mandate.Challenge.read (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more)
      (IncidentWithdrawalNative.attemptPosition model start pastStages vocabulary encoding law ready rival more) = none := by
    simp only [Mandate.Challenge.read, dif_neg unsigned]
  have noRenew : Mandate.Challenge.readReconfirmation (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim
      (IncidentWithdrawalNative.attemptPosition model start pastStages vocabulary encoding law ready rival more) = none := by
    simp only [Mandate.Challenge.readReconfirmation, noClaim]
  have nativeValid : (Mandate.law model.base model.scope).Valid (attempt.position.item _ _).before (attempt.position.item _ _).request ↔
      model.source.code.law.Valid (attemptItem model start pastStages vocabulary encoding law ready).before
        (attemptItem model start pastStages vocabulary encoding law ready).request := by
    rw [attemptPosition, originalItem, ← model.law_exact]
  refine ⟨?_, ?_, fun denied => model.source.code.law.rejected_preserves_current _ _ denied⟩
  · simp only [Mandate.Challenge.History.initial, Mandate.Challenge.History.receive, noRenew,
      Mandate.Challenge.Target.claim, decoded]
    split <;> rename_i accepted
    · simp only [Mandate.Challenge.History.isPending]
      simp [nativeValid.mp accepted]
    · have denied := fun valid => accepted (nativeValid.mpr valid)
      simp only [Mandate.Challenge.History.isPending]
      have rejected : decide (model.source.code.law.Valid (attemptItem model start pastStages vocabulary encoding law ready).before
          (attemptItem model start pastStages vocabulary encoding law ready).request) = false := decide_eq_false_iff_not.mpr denied
      rw [rejected]
      rfl
  · intro valid
    have effect := attempt.actual_withdrawal (family model start pastStages vocabulary encoding law ready rival more)
      (sourceIndex model start pastStages vocabulary encoding law ready rival more) claim (nativeValid.mpr valid)
    rw [attemptPosition, originalItem, ← model.law_exact] at effect
    exact effect

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentWithdrawalNative
