import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Validation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Contract

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit

theorem actual_word (depth : Nat) (started : 10 ≤ depth) :
    (source.actualExecution depth).submitted = (respond (source.currentAt (depth + 1))).word := by
  rw [source.actual_execution_word, ← (source.canonical_frame (depth + 1)).2]
  have complete := source.completion_persists 2 (depth - 1) original_service_paid
  exact source.completed_word_is_source_continuation (depth + 1) 0 (by omega)
    (by simpa only [show 2 + (depth - 1) = depth + 1 by omega] using complete) rfl

theorem actual_after (depth : Nat) (started : 10 ≤ depth) :
    (source.actualExecution depth).after =
      law.next (source.currentAt (depth + 1)) (respond (source.currentAt (depth + 1))).word := by
  rw [(source.actualExecution depth).after_exact, source.actual_execution_before,
    ← raw_current_frame, actual_word depth started]
  rfl

theorem next_word_uses_actual_after (depth : Nat) (started : 10 ≤ depth) :
    (source.actualExecution (depth + 1)).submitted = (respond (source.actualExecution depth).after).word := by
  rw [actual_word (depth + 1) (by omega), source.actual_execution_after, ← raw_current_frame]

theorem every_actual_response_keeps_old_claims (depth : Nat) (started : 10 ≤ depth) :
    (source.actualExecution depth).after.claims = (source.actualExecution depth).before.claims := by
  rw [actual_after depth started, source.actual_execution_before, ← raw_current_frame]
  exact response_keeps_all_financial_positions _ (by rw [source_round]; omega)

theorem actual_repair_contains_original_refusal (depth : Nat) (started : 10 ≤ depth)
    (missing : ¬ CopyResources (source.currentAt (depth + 1))
      (parent (source.currentAt (depth + 1))) (child (source.currentAt (depth + 1))))
    (failed : ExecutionItem Party Good Port Technology Unit)
    (original : failed ∈ law.rawItems (source.currentAt (depth + 1))
      (copy (parent (source.currentAt (depth + 1))) (child (source.currentAt (depth + 1)))))
    (refused : ¬ law.Valid failed.before failed.request)
    (selected : attemptCopy (source.currentAt (depth + 1)) (parent (source.currentAt (depth + 1)))
      (child (source.currentAt (depth + 1))) = .blocked failed original refused) :
    failed ∈ (source.actualExecution depth).interpreted.items ∧ ¬ law.Valid failed.before failed.request := by
  refine ⟨?_, refused⟩
  change failed ∈ law.rawItems (source.currentAt (depth + 1)) (source.actualExecution depth).submitted
  rw [actual_word depth started, repair_word _ missing (by rw [source_round]; omega)]
  exact rejected_candidate_is_in_repair_execution _ _ _ failed original refused selected

theorem actual_feedback_sequence :
    ((List.range 9).map fun offset => (respond (source.currentAt (offset + 11))).kind) =
      [.repair, .copied, .repair, .copied, .repair, .repair, .repair, .repair, .repair] := by
  calc
    _ = ((List.range 9).map fun offset => (respond (source.frameAt (offset + 11)).raw).kind) := by
      apply congrArg (fun fn : Nat → Kind => (List.range 9).map fn)
      funext offset
      rw [raw_current_frame]
    _ = _ := by decide +kernel

def birthVisit (which : Fin 2) : Nat := if which.val = 0 then 12 else 14
def newborn (which : Fin 2) : Party := if which.val = 0 then 6 else 7

theorem births_are_from_actual_shared_resources (which : Fin 2) :
    parent (source.currentAt (birthVisit which)) + 1 = newborn which ∧
    child (source.currentAt (birthVisit which)) = newborn which ∧
    CopyResources (source.currentAt (birthVisit which))
      (parent (source.currentAt (birthVisit which))) (newborn which) ∧
    (∀ good, (source.currentAt (birthVisit which)).stock (newborn which) good = 0) ∧
    (source.currentAt (birthVisit which + 1)).stock (newborn which) .seed = 3 ∧
    (source.currentAt (birthVisit which + 1)).stock (newborn which) .life = 5 ∧
    (source.currentAt (birthVisit which + 1)).stock (newborn which) .spare = 1 := by
  rcases which with ⟨value, bound⟩
  interval_cases value <;> simp only [birthVisit, newborn, raw_current_frame] <;> decide +kernel +revert

theorem original_waste_really_rebuilds_maintenance :
    (source.currentAt 13).stock 0 .waste = 1 ∧
    (source.currentAt 14).stock 0 .waste = 0 ∧
    (source.currentAt 13).stock 6 .spare = 1 ∧
    (source.currentAt 14).stock 6 .spare = 2 ∧
    (source.currentAt 13).stock 3 .energy - (source.currentAt 14).stock 3 .energy = 1 ∧
    (source.currentAt 13).stock 3 .labor - (source.currentAt 14).stock 3 .labor = 1 ∧
    (source.currentAt 14).claims = (source.currentAt 13).claims := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 6
  · have preserved := every_actual_response_keeps_old_claims 12 (by decide)
    rw [source.actual_execution_after, source.actual_execution_before,
      ← raw_current_frame, ← raw_current_frame] at preserved
    exact preserved
  all_goals simp only [raw_current_frame]; decide +kernel

def continuationItems := (List.range 19).flatMap fun ordinal =>
  law.rawItems (source.frameAt ordinal).raw (source.frameWord ordinal (source.frameAt ordinal))

theorem all_actual_cuts_preserve_living_floors :
    ∀ item ∈ continuationItems, ∀ actor ∈ ([0, 1, 2, 4, 5, 6, 7] : List Party),
      (actor ≤ 2 ∨ 0 < item.before.stock actor .seed →
        1 ≤ item.before.stock actor .life ∧ 1 ≤ item.before.stock actor .spare) ∧
      (actor ≤ 2 ∨ 0 < (law.step item.before item.request).stock actor .seed →
        1 ≤ (law.step item.before item.request).stock actor .life ∧
        1 ≤ (law.step item.before item.request).stock actor .spare) := by
  decide +kernel

theorem exhausted_resources_remain_explicit :
    (respond (source.currentAt 19)).kind = .repair ∧
    parent (source.currentAt 19) = 7 ∧ child (source.currentAt 19) = 8 ∧
    (source.currentAt 19).stock 7 .feed = 7 ∧ (source.currentAt 19).stock 7 .labor = 0 ∧
    (source.currentAt 19).stock 7 .spare = 1 ∧
    (source.currentAt 19).stock 8 .seed = 0 ∧
    ((deficits (source.currentAt 19) 7).map fun gap => (gap.good, gap.required - (source.currentAt 19).stock 7 gap.good)) =
      [(.feed, 1), (.labor, 2), (.spare, 1)] := by
  simp only [raw_current_frame]
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback
