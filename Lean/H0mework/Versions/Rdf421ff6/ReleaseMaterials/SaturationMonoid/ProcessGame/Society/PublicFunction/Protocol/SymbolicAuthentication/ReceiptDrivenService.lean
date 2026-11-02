import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenExecution

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenService
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

section Intent
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)
  (start : Cursor code) (entry : List (EventHistory.Stage (code := code)))

theorem a_required_authenticated_intent_is_the_original_local_word (site : Fin code.sites)
    (needed : RetainedIntent.intent vocabulary encoding law start entry site ≠ []) :
    RetainedIntent.intent vocabulary encoding law start entry site =
      RequestResponse.work site (RetainedIntent.memory start entry site) := by
  unfold RetainedIntent.intent ReceivedStatementAuthentication.work at needed ⊢
  split_ifs at needed ⊢ <;> simp_all

theorem an_empty_local_word_has_no_authenticated_intent (site : Fin code.sites)
    (empty : RequestResponse.work site (RetainedIntent.memory start entry site) = []) :
    RetainedIntent.intent vocabulary encoding law start entry site = [] := by
  simp only [RetainedIntent.intent, ReceivedStatementAuthentication.work, empty, if_true]

end Intent

open ReceiptDrivenSource

-- This table inspects actual local records, without enumerating possible
-- communication histories or assuming that any authentication check succeeds.
theorem only_two_actual_snapshots_can_require_a_response :
    ∀ index ∈ List.range 17, ∀ site : Fin (code .normal).sites,
      RequestResponse.work site (RetainedIntent.memory (start .normal 16) (ReceiptDrivenTrace.stages.take index) site) ≠ [] →
      (index = 6 ∧ site = 1) ∨ (index = 10 ∧ site = 1) := by decide +kernel

theorem the_actual_snapshot_rule_is_the_complete_authenticated_rule
    (index : Nat) (atCut : index = 6 ∨ index = 10)
    (needed : RetainedIntent.intent vocabulary (encoding .normal) (law .normal) (start .normal 16)
      (ReceiptDrivenTrace.stages.take index) 1 ≠ []) :
    ReceiptDrivenTrace.ruleAt index = RetainedIntent.protocol vocabulary (encoding .normal) (law .normal)
      (start .normal 16) (ReceiptDrivenTrace.stages.take index) := by
  have word := a_required_authenticated_intent_is_the_original_local_word vocabulary (encoding .normal) (law .normal)
    (start .normal 16) (ReceiptDrivenTrace.stages.take index) 1 needed
  have other : RetainedIntent.intent vocabulary (encoding .normal) (law .normal) (start .normal 16)
      (ReceiptDrivenTrace.stages.take index) 0 = [] := by
    apply an_empty_local_word_has_no_authenticated_intent
    rcases atCut with rfl | rfl <;> decide +kernel
  have memory : RetainedIntent.memory (start .normal 16) (ReceiptDrivenTrace.stages.take index) =
      (fun site => if site = 1 then (if index = 6 then 1 else 2) else 0) := by
    rcases atCut with rfl | rfl <;> funext site <;> fin_cases site <;> decide +kernel
  rw [memory] at word
  apply LocalRuleTable.verified_table_is_the_entire_original_rule
  unfold LocalRuleTable.verify
  apply List.all_eq_true.mpr
  rintro ⟨⟨site, signal⟩, inside⟩ _
  rcases atCut with rfl | rfl
  all_goals
    fin_cases site <;> fin_cases signal <;>
      simp [ReceiptDrivenTrace.ruleAt, ReceiptDrivenTrace.response, RetainedIntent.protocol,
        RetainedIntent.policy, RetainedIntent.work, word, other] <;> decide +kernel


def rowAt (index : Nat) := StageTrace.material (EventHistory.execute (start .normal 16)
  (ReceiptDrivenTrace.stages.take index)) (ReceiptDrivenTrace.ruleAt index) (EventStep.fixed (ReceiptDrivenTrace.moveAt index))

theorem each_response_is_a_valid_owned_submission_in_the_original_history :
    ∀ index ∈ [6, 10],
      (StageTrace.records (start .normal 16) ReceiptDrivenTrace.stages)[index]? = some (rowAt index) ∧
      StageTrace.activation (rowAt index) = some 1 ∧
      (rowAt index).submitted = RequestResponse.work 1
        (RetainedIntent.memory (start .normal 16) (ReceiptDrivenTrace.stages.take index) 1) ∧
      (∀ item ∈ StageTrace.items (rowAt index), (code .normal).law.Valid item.before item.request) ∧
      ReceiptDrivenTrace.stages[index]? =
        some (ReceiptDrivenTrace.ruleAt index, EventStep.fixed (ReceiptDrivenTrace.moveAt index)) := by
  intro index member
  have atCut : index = 6 ∨ index = 10 := by simpa using member
  rcases atCut with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals first | rfl | decide +kernel

theorem every_actual_snapshot_has_its_own_valid_complete_service :
    InterferenceValidity.closed (model .normal) (start .normal 16) vocabulary (encoding .normal) (law .normal)
      (LocalWindowRun.audit (model .normal) ReceiptDrivenTrace.stages []) := by
  intro entry registered site needed
  obtain ⟨index, bounded, same⟩ := List.mem_map.mp registered
  subst entry
  have bound : index ∈ List.range 17 := by simpa [ReceiptDrivenTrace.stages, ReceiptDrivenTrace.slots,
    ReceiptDrivenMaterialization.extend] using bounded
  have rawNeeded : RequestResponse.work site (RetainedIntent.memory (start .normal 16)
      (ReceiptDrivenTrace.stages.take index) site) ≠ [] := by
    rw [← a_required_authenticated_intent_is_the_original_local_word vocabulary (encoding .normal) (law .normal)
      (start .normal 16) (ReceiptDrivenTrace.stages.take index) site needed]
    exact needed
  have classified := only_two_actual_snapshots_can_require_a_response index bound site rawNeeded
  have atCut : index = 6 ∨ index = 10 := classified.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have owner : site = 1 := classified.elim And.right And.right
  subst site
  have member : index ∈ [6, 10] := by simpa using atCut
  obtain ⟨actualRow, activated, rawWord, valid, actualStage⟩ :=
    each_response_is_a_valid_owned_submission_in_the_original_history index member
  refine ⟨index, ?_, List.length_take_le .., rowAt index, actualRow, activated, ?_, valid,
    (ReceiptDrivenTrace.ruleAt index, EventStep.fixed (ReceiptDrivenTrace.moveAt index)), actualStage, ?_⟩
  · rcases atCut with rfl | rfl <;> decide +kernel
  · exact rawWord.trans (a_required_authenticated_intent_is_the_original_local_word vocabulary (encoding .normal)
      (law .normal) (start .normal 16) (ReceiptDrivenTrace.stages.take index) 1 needed).symm
  · exact (IncidentResponse.sameRule_iff _ _ _).mpr
      (the_actual_snapshot_rule_is_the_complete_authenticated_rule index atCut needed)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenService
