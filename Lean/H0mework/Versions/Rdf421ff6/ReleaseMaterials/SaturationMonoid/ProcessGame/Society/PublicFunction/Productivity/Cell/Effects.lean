import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Source
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Exit
open OutstandingSource.NativeService

def child (which : Fin 2) : Party := if which.val = 0 then 1 else 2
def descendant (which : Fin 2) : Party := if which.val = 0 then 4 else 5
def birthVisit (which : Fin 2) : Nat := if which.val = 0 then 4 else 7
def firstVisit (which : Fin 2) : Nat := if which.val = 0 then 6 else 8
def copyVisit (which : Fin 2) : Nat := if which.val = 0 then 9 else 10

theorem source_round (ordinal : Nat) : (source.currentAt ordinal).round = ordinal := by
  have generated := source.current_round ordinal
  change (source.currentAt ordinal).round = 0 + ordinal at generated
  simpa only [Nat.zero_add] using generated

theorem all_stages_ready (stage : Fin 9) : Ready (source.currentAt (stage.val + 2)) := by
  rcases stage with ⟨value, bound⟩
  interval_cases value <;> rw [raw_current_frame] <;> decide +kernel +revert

theorem actual_candidate (stage : Fin 9) :
    (source.actualExecution (stage.val + 1)).submitted = candidate (source.currentAt (stage.val + 2)) := by
  have emitted := continuation_is_actual (stage.val + 2) (by omega)
  rw [show stage.val + 2 - 1 = stage.val + 1 by omega] at emitted
  have before : (source.currentAt (stage.val + 2)).round ≤ 10 := by rw [source_round]; omega
  simpa only [Feedback.respond, if_pos before, Feedback.Outcome.word,
    respond, dif_pos (all_stages_ready stage), Response.word] using emitted

theorem actual_next (stage : Fin 9) :
    source.currentAt (stage.val + 3) =
      law.next (source.currentAt (stage.val + 2)) (candidate (source.currentAt (stage.val + 2))) := by
  rw [raw_current_frame, ← source.actual_execution_after (stage.val + 1),
    (source.actualExecution (stage.val + 1)).after_exact, source.actual_execution_before,
    ← raw_current_frame, actual_candidate]
  rfl

theorem actual_copy_word (which : Fin 2) :
    (source.actualExecution (copyVisit which - 1)).submitted = copy (child which) (descendant which) := by
  rcases which with ⟨value, bound⟩
  interval_cases value
  · simpa [copyVisit, child, descendant, candidate, source_round] using actual_candidate ⟨7, by decide⟩
  · simpa [copyVisit, child, descendant, candidate, source_round] using actual_candidate ⟨8, by decide⟩

theorem opening_and_research_are_paid :
    (source.currentAt 2).technology = (false, false) ∧
    (source.currentAt 3).technology = (true, false) ∧
    (source.currentAt 2).stock 0 .energy - (source.currentAt 3).stock 0 .energy = 1 ∧
    (source.currentAt 2).stock 0 .labor - (source.currentAt 3).stock 0 .labor = 1 ∧
    (source.currentAt 5).technology = (true, false) ∧
    (source.currentAt 6).technology = (true, true) ∧
    (source.currentAt 5).stock 1 .feed - (source.currentAt 6).stock 1 .feed = 1 ∧
    (source.currentAt 5).stock 1 .energy - (source.currentAt 6).stock 1 .energy = 1 ∧
    (source.currentAt 5).stock 1 .labor - (source.currentAt 6).stock 1 .labor = 1 := by
  simp only [raw_current_frame]
  decide +kernel

theorem mother_production_settles_the_original_loan :
    (source.currentAt 0).claims () 0 2 = 0 ∧
    (source.currentAt 2).claims () 0 2 = 1 ∧
    (source.currentAt 4).claims () 0 2 = 0 ∧
    (source.currentAt 2).stock 0 .seed = 1 ∧
    (source.currentAt 4).stock 0 .seed = 3 ∧
    (source.currentAt 4).stock 2 .life = 2 := by
  simp only [raw_current_frame]
  decide +kernel

theorem actual_seed_and_first_cycle (which : Fin 2) :
    (source.currentAt (birthVisit which)).stock (child which) .seed = 0 ∧
    (source.currentAt (birthVisit which + 1)).stock (child which) .seed = 1 ∧
    (source.currentAt (birthVisit which)).stock 0 .seed -
      (source.currentAt (birthVisit which + 1)).stock 0 .seed = 1 ∧
    (source.currentAt (firstVisit which + 1)).stock (child which) .seed = 3 ∧
    Necessity.AllNeedsPaid law (source.currentAt (firstVisit which)) [child which]
      (candidate (source.currentAt (firstVisit which))) := by
  rcases which with ⟨value, bound⟩
  interval_cases value <;>
    simp only [birthVisit, firstVisit, child, raw_current_frame] <;> decide +kernel +revert

theorem actual_second_generation (which : Fin 2) :
    (source.currentAt (copyVisit which)).stock (descendant which) .seed = 0 ∧
    (source.currentAt (copyVisit which + 1)).stock (descendant which) .seed = 3 ∧
    (source.currentAt (copyVisit which + 1)).stock (descendant which) .life = 5 ∧
    (source.currentAt (copyVisit which + 1)).stock (descendant which) .spare = 1 ∧
    (source.currentAt (copyVisit which)).stock (child which) .labor -
      (source.currentAt (copyVisit which + 1)).stock (child which) .labor = 2 ∧
    Necessity.AllNeedsPaid law (source.currentAt (copyVisit which)) [descendant which]
      (candidate (source.currentAt (copyVisit which))) ∧
    (∀ request ∈ candidate (source.currentAt (copyVisit which)),
      request.signer = child which ∨ request.signer = descendant which) := by
  rcases which with ⟨value, bound⟩
  interval_cases value <;>
    simp only [copyVisit, child, descendant, raw_current_frame] <;> decide +kernel +revert

def Floor (current : Current) : Prop :=
  ∀ actor ∈ ([0, 1, 2] : List Party), 1 ≤ current.stock actor .life ∧ 1 ≤ current.stock actor .spare

instance (current : Current) : Decidable (Floor current) := by unfold Floor; infer_instance

def migrationItems := (List.range 11).flatMap fun ordinal =>
  law.rawItems (source.frameAt ordinal).raw (source.frameWord ordinal (source.frameAt ordinal))

theorem every_migration_cut_keeps_the_original_bearers :
    Floor initial ∧ Floor (source.currentAt 11) ∧
    ∀ item ∈ migrationItems, Floor item.before ∧ Floor (law.step item.before item.request) := by
  simp only [raw_current_frame]
  decide +kernel

theorem newborns_keep_life_and_maintenance_after_seeding :
    ∀ item ∈ migrationItems, ∀ actor ∈ ([4, 5] : List Party),
      (0 < item.before.stock actor .seed →
        1 ≤ item.before.stock actor .life ∧ 1 ≤ item.before.stock actor .spare) ∧
      (0 < (law.step item.before item.request).stock actor .seed →
        1 ≤ (law.step item.before item.request).stock actor .life ∧
          1 ≤ (law.step item.before item.request).stock actor .spare) := by
  decide +kernel

def totalStock (current : Current) (goods : List Good) : ℚ :=
  ((List.finRange 6).map fun actor => (goods.map (current.stock actor)).sum).sum

theorem finite_material_and_work_account :
    totalStock initial [.seed, .feed, .life, .spare, .waste] = 83 ∧
    totalStock (source.currentAt 11) [.seed, .feed, .life, .spare, .waste] = 66 ∧
    totalStock initial [.energy] - totalStock (source.currentAt 11) [.energy] = 7 ∧
    totalStock initial [.labor] - totalStock (source.currentAt 11) [.labor] = 11 ∧
    totalStock (source.currentAt 11) [.seed] = 11 ∧
    totalStock (source.currentAt 11) [.waste] = 1 ∧
    (source.currentAt 11).claims () 0 2 = 0 := by
  simp only [raw_current_frame]
  decide +kernel

theorem original_service_archives_survive (index : source.Slot) (later : Nat) :
    (historyAt source index (1 + later)).state = (historyAt source index 1).state := by
  apply terminal_state_is_preserved source index 1 later
  apply (native_terminal_iff_recorded source index 1).mpr
  refine ⟨1, ?_⟩
  rcases index with ⟨value, bound⟩
  change value < 6 at bound
  interval_cases value <;> decide +kernel +revert

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell
