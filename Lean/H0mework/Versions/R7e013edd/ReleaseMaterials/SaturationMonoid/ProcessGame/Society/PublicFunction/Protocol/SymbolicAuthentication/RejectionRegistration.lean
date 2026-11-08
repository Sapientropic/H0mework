import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdaptiveRejectionClaims
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionRegistration
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

-- Prove the invariant of the existing scan; do not replace its response producer.
open private register scan scan_append planAt_never_selects_a_handled_rejection from
  H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionResponse

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

private theorem register_keeps_distinct_identities
    (past : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (RejectionResponse.Answer model start vocabulary encoding law))
    (stage : EventHistory.Stage (code := model.source.code))
    (distinct : (answers.map (RejectionResponse.Answer.id model start vocabulary encoding law)).Nodup) :
    ((register model start vocabulary encoding law past answers stage).map
      (RejectionResponse.Answer.id model start vocabulary encoding law)).Nodup := by
  unfold register
  split
  · rename_i response selected
    split
    · have fresh := planAt_never_selects_a_handled_rejection model start past vocabulary encoding law response
        (answers.map (RejectionResponse.Answer.id model start vocabulary encoding law)) selected
      simp only [List.map_append, List.map_cons, List.map_nil, RejectionResponse.Answer.id]
      apply List.nodup_append.mpr
      refine ⟨distinct, by simp, ?_⟩
      intro id member other singleton same
      obtain rfl := List.mem_singleton.mp singleton
      exact fresh (same ▸ member)
    · exact distinct
  · exact distinct

private theorem scan_keeps_distinct_identities
    (past tail : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (RejectionResponse.Answer model start vocabulary encoding law))
    (distinct : (answers.map (RejectionResponse.Answer.id model start vocabulary encoding law)).Nodup) :
    ((scan model start vocabulary encoding law past answers tail).map
      (RejectionResponse.Answer.id model start vocabulary encoding law)).Nodup := by
  induction tail generalizing past answers with
  | nil => exact distinct
  | cons stage tail ih =>
    exact ih (past ++ [stage]) _ (register_keeps_distinct_identities model start vocabulary encoding law past answers stage distinct)

theorem the_original_journal_never_registers_one_identity_twice
    (past : List (EventHistory.Stage (code := model.source.code))) :
    ((RejectionResponse.journal model start past vocabulary encoding law).map
      (RejectionResponse.Answer.id model start vocabulary encoding law)).Nodup :=
  scan_keeps_distinct_identities model start vocabulary encoding law [] past [] (by simp)

private theorem scan_preserves_answers
    (past tail : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (RejectionResponse.Answer model start vocabulary encoding law)) :
    answers <+: scan model start vocabulary encoding law past answers tail := by
  induction tail generalizing past answers with
  | nil => exact List.prefix_refl _
  | cons stage tail ih =>
    have kept : answers <+: register model start vocabulary encoding law past answers stage := by
      unfold register
      split
      · split
        · exact List.prefix_append _ _
        · exact List.prefix_refl _
      · exact List.prefix_refl _
    exact kept.trans (ih (past ++ [stage]) _)

theorem actual_history_extension_preserves_the_literal_original_journal
    (past more : List (EventHistory.Stage (code := model.source.code))) :
    RejectionResponse.journal model start past vocabulary encoding law <+:
      RejectionResponse.journal model start (past ++ more) vocabulary encoding law := by
  unfold RejectionResponse.journal
  rw [scan_append]
  exact scan_preserves_answers model start vocabulary encoding law _ more _

theorem the_number_of_actual_native_responses_has_the_original_source_budget
    (past : List (EventHistory.Stage (code := model.source.code)))
    (allowance : Nat) (compliant : AdaptiveRejectionHistory.Compliant start allowance past) :
    (RejectionResponse.journal model start past vocabulary encoding law).length ≤
      AdaptiveReceptionBudget.capacity (code := model.source.code) := by
  have paid := AdaptiveRejectionClaims.distinct_native_response_identities_have_the_same_source_budget
    vocabulary model start past encoding law allowance compliant
  rw [List.toFinset_card_of_nodup
    (the_original_journal_never_registers_one_identity_twice model start vocabulary encoding law past), List.length_map] at paid
  exact paid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RejectionRegistration
