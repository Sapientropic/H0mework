import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenService

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 65536
set_option maxHeartbeats 60000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowService
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open ReceiptDrivenSource ReceiptWindowSource

abbrev window (timing : Timing) (second : Bool) (index : Nat) :=
  deliveryAt timing second + 1 ≤ index ∧ index ≤ replyAt timing second
def reading (second : Bool) : Fin (code .normal).signals := if second then 2 else 1

theorem every_possible_local_responsibility_is_in_its_actual_service_window :
    ∀ timing : Timing, ∀ index ∈ List.range 25, ∀ site : Fin (code .normal).sites,
      RequestResponse.work site (RetainedIntent.memory initial (stages timing |>.take index) site) ≠ [] →
      site = 1 ∧ (window timing false index ∨ window timing true index) := by
  rintro ⟨a, b⟩
  cases a <;> cases b <;> decide +kernel

theorem every_window_preserves_the_original_local_record :
    ∀ timing : Timing, ∀ second : Bool, ∀ index ∈ List.range 25, window timing second index →
      ∀ site : Fin (code .normal).sites,
        RetainedIntent.memory initial (stages timing |>.take index) site =
          if site = 1 then reading second else 0 := by
  rintro ⟨a, b⟩ second
  cases a <;> cases b <;> cases second <;> decide +kernel

theorem the_complete_authenticated_rule_is_the_actual_response_rule
    (entry : ReceiptBranchCoverage.Stages (model .normal)) (second : Bool)
    (memory : RetainedIntent.memory initial entry = fun site => if site = 1 then reading second else 0)
    (needed : RetainedIntent.intent vocabulary (encoding .normal) (law .normal) initial entry 1 ≠ []) :
    ReceiptDrivenTrace.response (reading second) =
      RetainedIntent.protocol vocabulary (encoding .normal) (law .normal) initial entry := by
  have word := ReceiptDrivenService.a_required_authenticated_intent_is_the_original_local_word
    vocabulary (encoding .normal) (law .normal) initial entry 1 needed
  have other : RetainedIntent.intent vocabulary (encoding .normal) (law .normal) initial entry 0 = [] := by
    apply ReceiptDrivenService.an_empty_local_word_has_no_authenticated_intent
    rw [memory]
    change RequestResponse.work 0 0 = []
    decide +kernel
  rw [memory] at word
  have memoryAt (site : Fin (code .normal).sites) := congrFun memory site
  apply LocalRuleTable.verified_table_is_the_entire_original_rule
  unfold LocalRuleTable.verify
  apply List.all_eq_true.mpr
  rintro ⟨⟨site, signal⟩, inside⟩ _
  cases second <;> fin_cases site <;> fin_cases signal
  all_goals
    simp only [RetainedIntent.protocol, RetainedIntent.policy, RetainedIntent.work]
    simp [ReceiptDrivenTrace.response, reading, word, other, memoryAt] <;> decide +kernel

def rowAt (timing : Timing) (second : Bool) := StageTrace.material
  (EventHistory.execute initial (stages timing |>.take (replyAt timing second)))
  (ruleAt timing (replyAt timing second)) (EventStep.fixed (moveAt timing (replyAt timing second)))

theorem every_service_is_an_original_valid_owned_submission :
    ∀ timing : Timing, ∀ second : Bool,
      (StageTrace.records initial (stages timing))[replyAt timing second]? = some (rowAt timing second) ∧
      StageTrace.activation (rowAt timing second) = some 1 ∧
      (rowAt timing second).submitted = RequestResponse.work 1 (reading second) ∧
      (∀ item ∈ StageTrace.items (rowAt timing second), (code .normal).law.Valid item.before item.request) ∧
      (stages timing)[replyAt timing second]? =
        some (ruleAt timing (replyAt timing second), EventStep.fixed (moveAt timing (replyAt timing second))) ∧
      ruleAt timing (replyAt timing second) = ReceiptDrivenTrace.response (reading second) := by
  rintro ⟨a, b⟩ second
  cases a <;> cases b <;> cases second
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | rfl | decide +kernel

theorem every_original_snapshot_has_its_own_valid_complete_service (timing : Timing) :
    InterferenceValidity.closed (model .normal) initial vocabulary (encoding .normal) (law .normal)
      (LocalWindowRun.audit (model .normal) (stages timing) []) := by
  intro entry registered site needed
  obtain ⟨index, bound, same⟩ := List.mem_map.mp registered
  subst entry
  have bounded : index ∈ List.range 25 := by simpa [stages, horizon, separation, cycle, allowance] using bound
  have rawNeeded : RequestResponse.work site (RetainedIntent.memory initial (stages timing |>.take index) site) ≠ [] := by
    rw [← ReceiptDrivenService.a_required_authenticated_intent_is_the_original_local_word vocabulary (encoding .normal)
      (law .normal) initial (stages timing |>.take index) site needed]
    exact needed
  obtain ⟨owner, either⟩ := every_possible_local_responsibility_is_in_its_actual_service_window timing index bounded site rawNeeded
  have existsWindow : ∃ second : Bool, window timing second index := either.elim (fun h => ⟨false, h⟩) (fun h => ⟨true, h⟩)
  obtain ⟨second, within⟩ := existsWindow
  subst site
  have memory : RetainedIntent.memory initial (stages timing |>.take index) =
      fun site => if site = 1 then reading second else 0 := by
    funext site
    exact every_window_preserves_the_original_local_record timing second index bounded within site
  have word := ReceiptDrivenService.a_required_authenticated_intent_is_the_original_local_word vocabulary (encoding .normal)
    (law .normal) initial (stages timing |>.take index) 1 needed
  rw [memory] at word
  simp only [ite_true] at word
  obtain ⟨actualRow, activated, rawWord, valid, actualStage, rule⟩ :=
    every_service_is_an_original_valid_owned_submission timing second
  refine ⟨replyAt timing second, ?_, (List.length_take_le ..).trans within.2,
    rowAt timing second, actualRow, activated, rawWord.trans word.symm, valid,
    (ruleAt timing (replyAt timing second), EventStep.fixed (moveAt timing (replyAt timing second))), actualStage, ?_⟩
  · rcases timing with ⟨a, b⟩
    cases a <;> cases b <;> cases second <;> decide +kernel
  · apply (IncidentResponse.sameRule_iff _ _ _).mpr
    exact rule.trans (the_complete_authenticated_rule_is_the_actual_response_rule _ second memory needed)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptWindowService
