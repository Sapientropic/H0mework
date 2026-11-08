import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentInventory
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentRegistration
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

-- Prove the invariant of the existing scan; do not replace its response producer.
open private register scan scan_append planAt_never_selects_a_handled_incident from
  H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentResponse

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
    (answers : List (IncidentResponse.Answer model start vocabulary encoding law))
    (stage : EventHistory.Stage (code := model.source.code))
    (distinct : (answers.map (IncidentResponse.Answer.id model start vocabulary encoding law)).Nodup) :
    ((register model start vocabulary encoding law past answers stage).map
      (IncidentResponse.Answer.id model start vocabulary encoding law)).Nodup := by
  unfold register
  split
  · rename_i response selected
    split
    · have fresh := planAt_never_selects_a_handled_incident model start past vocabulary encoding law response
        (answers.map (IncidentResponse.Answer.id model start vocabulary encoding law)) selected
      simp only [List.map_append, List.map_cons, List.map_nil, IncidentResponse.Answer.id]
      apply List.nodup_append.mpr
      refine ⟨distinct, by simp, ?_⟩
      intro id member other singleton same
      obtain rfl := List.mem_singleton.mp singleton
      exact fresh (same ▸ member)
    · exact distinct
  · exact distinct

private theorem scan_keeps_distinct_identities
    (past tail : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (IncidentResponse.Answer model start vocabulary encoding law))
    (distinct : (answers.map (IncidentResponse.Answer.id model start vocabulary encoding law)).Nodup) :
    ((scan model start vocabulary encoding law past answers tail).map
      (IncidentResponse.Answer.id model start vocabulary encoding law)).Nodup := by
  induction tail generalizing past answers with
  | nil => exact distinct
  | cons stage tail ih =>
    exact ih (past ++ [stage]) _ (register_keeps_distinct_identities model start vocabulary encoding law past answers stage distinct)

theorem the_original_journal_never_registers_one_identity_twice
    (past : List (EventHistory.Stage (code := model.source.code))) :
    ((IncidentResponse.journal model start past vocabulary encoding law).map
      (IncidentResponse.Answer.id model start vocabulary encoding law)).Nodup :=
  scan_keeps_distinct_identities model start vocabulary encoding law [] past [] (by simp)

private theorem scan_preserves_answers
    (past tail : List (EventHistory.Stage (code := model.source.code)))
    (answers : List (IncidentResponse.Answer model start vocabulary encoding law)) :
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
    IncidentResponse.journal model start past vocabulary encoding law <+:
      IncidentResponse.journal model start (past ++ more) vocabulary encoding law := by
  unfold IncidentResponse.journal
  rw [scan_append]
  exact scan_preserves_answers model start vocabulary encoding law _ more _

theorem every_registered_incident_retains_its_original_budget_identity
    (past : List (EventHistory.Stage (code := model.source.code)))
    (answer : IncidentResponse.Answer model start vocabulary encoding law)
    (inside : answer ∈ IncidentResponse.journal model start past vocabulary encoding law) :
    IncidentResponse.Answer.id model start vocabulary encoding law answer ∈
      IncidentBirth.identities start vocabulary encoding law past := by
  have source : answer.pastStages <+: past := (List.prefix_append _ _).trans
    (IncidentResponse.every_answer_retains_its_actual_source_prefix model start past vocabulary encoding law answer inside)
  obtain ⟨more, actual⟩ := source
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨answer.response.incident, ?_, rfl⟩
  rw [← actual, StageAccountability.ledger_extends_by_its_generated_next]
  exact List.mem_append_left _ answer.response.actual

theorem the_number_of_actual_native_responses_has_the_original_source_budget
    (past : List (EventHistory.Stage (code := model.source.code))) :
    (IncidentResponse.journal model start past vocabulary encoding law).length ≤
      IncidentInventory.capacity (code := model.source.code) := by
  have included : ((IncidentResponse.journal model start past vocabulary encoding law).map
      (IncidentResponse.Answer.id model start vocabulary encoding law)).toFinset ⊆
        IncidentBirth.identities start vocabulary encoding law past := by
    intro identity member
    obtain ⟨answer, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact every_registered_incident_retains_its_original_budget_identity model start vocabulary encoding law past answer inside
  have paid := (Finset.card_le_card included).trans
    (IncidentInventory.all_actual_incident_identities_have_a_source_generated_budget encoding start vocabulary law past)
  rw [List.toFinset_card_of_nodup
    (the_original_journal_never_registers_one_identity_twice model start vocabulary encoding law past), List.length_map] at paid
  exact paid

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.IncidentRegistration
