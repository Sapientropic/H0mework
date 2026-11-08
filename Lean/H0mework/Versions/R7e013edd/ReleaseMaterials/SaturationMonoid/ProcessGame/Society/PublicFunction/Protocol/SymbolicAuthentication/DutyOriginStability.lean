import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.MixedFundedEntry

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyOriginStability
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (start : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code))

theorem an_actual_activation_has_no_outgoing_content
    (row : StageTrace.Record (code := code)) (worker : Fin code.sites)
    (active : StageTrace.activation row = some worker) : StageTransport.outgoing row = none := by
  unfold StageTrace.activation at active
  split at active <;> try contradiction
  split at active <;> try contradiction
  rename_i site event call same
  simp only [StageTransport.outgoing, call, same]

theorem an_actual_quiet_stage_has_no_outgoing_content
    (cursor : Cursor code) (rival : Opponent code) :
    StageTransport.outgoing (StageTrace.material cursor SilentWindow.quiet rival) = none := by
  by_cases stopped : (EventStep.seed cursor).remaining = 0
  · simp [StageTransport.outgoing, StageTrace.material, StageTrace.capture, stopped]
  · cases owner : Distributed.Recall.Information.Agency.ownerAt code cursor.ownerStart
        (EventStep.seed cursor).history.length <;>
      simp [StageTransport.outgoing, StageTrace.material, StageTrace.capture, stopped, owner,
        localEvent, SilentWindow.quiet]

theorem no_outgoing_stage_preserves_the_original_content_origins
    (past : List (EventHistory.Stage (code := code))) (protocol : Rule code) (rival : Opponent code)
    (noSend : StageTransport.outgoing (StageTrace.material (EventHistory.execute start past) protocol rival) = none) :
    StageDuty.origins start vocabulary encoding (past ++ [(protocol, rival)]) =
      StageDuty.origins start vocabulary encoding past := by
  have noIssue : StageTransport.issuedAt vocabulary encoding start (past ++ [(protocol, rival)]) past.length = none := by
    simp [StageTransport.issuedAt, StageQueue.records_append, StageTrace.records, StageTrace.record_count,
      StageTransport.issue, noSend]
  have noBirth : StageDuty.birth start vocabulary encoding (past ++ [(protocol, rival)]) past.length = none := by
    have full : (past ++ [(protocol, rival)]).take (past.length + 1) = past ++ [(protocol, rival)] :=
      List.take_of_length_le (by simp)
    cases born : StageDuty.birth start vocabulary encoding (past ++ [(protocol, rival)]) past.length with
    | none => rfl
    | some emission =>
      have original := StageDuty.birth_is_the_original_prefix start vocabulary encoding _ _ emission born
      have generated := emission.generated
      rw [original.1, original.2, full, noIssue] at generated
      cases generated
  unfold StageDuty.origins
  simp only [List.length_append, List.length_singleton, List.range_succ, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, noBirth, List.append_nil]
  apply List.filterMap_congr
  intro index inside
  exact StageDuty.birth_survives_extension start vocabulary encoding past [(protocol, rival)] index (List.mem_range.mp inside)

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (cursor : Cursor model.source.code)
  (encode : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem empty_duties_mean_every_original_content_is_confirmed
    (past : JointResponse.Stages model)
    (empty : UnifiedResponse.duties model cursor vocabulary encode law past = [])
    (emission : StageDuty.Emission cursor vocabulary encode)
    (original : emission ∈ StageDuty.origins cursor vocabulary encode past) :
    TimedDuty.Confirmed cursor past vocabulary encode law emission := by
  by_contra missing
  have inside : emission ∈ UnifiedResponse.duties model cursor vocabulary encode law past :=
    List.mem_filter.mpr ⟨original, decide_eq_true missing⟩
  rw [empty] at inside
  exact List.not_mem_nil inside

theorem no_outgoing_stage_preserves_confirmed_content
    (past : JointResponse.Stages model) (protocol : Rule model.source.code) (rival : Opponent model.source.code)
    (empty : UnifiedResponse.duties model cursor vocabulary encode law past = [])
    (noSend : StageTransport.outgoing (StageTrace.material (EventHistory.execute cursor past) protocol rival) = none) :
    UnifiedResponse.duties model cursor vocabulary encode law (past ++ [(protocol, rival)]) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro emission member
  obtain ⟨original, missing⟩ := List.mem_filter.mp member
  rw [no_outgoing_stage_preserves_the_original_content_origins cursor vocabulary encode past protocol rival noSend] at original
  exact (of_decide_eq_true missing) (DutyConfirmation.the_actual_confirmation_survives_extension
    cursor vocabulary encode law past [(protocol, rival)] emission
    (empty_duties_mean_every_original_content_is_confirmed vocabulary model cursor encode law past empty emission original))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DutyOriginStability
