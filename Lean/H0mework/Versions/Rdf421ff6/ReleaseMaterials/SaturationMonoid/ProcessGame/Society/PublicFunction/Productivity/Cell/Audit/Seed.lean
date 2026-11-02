import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Cuts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit

open Institutions.Capitalism.Universal.Source.Program

def seedCheck (count : Nat) : Bool := (Feedback.receipts count).all fun item =>
  (actors count).all fun actor => decide
    (0 < item.before.stock actor .seed → 0 < (law.step item.before item.request).stock actor .seed)

theorem checked_seeds_persist_for_every_address (count : Nat) (checked : seedCheck count = true)
    (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ Feedback.receipts count)
    (actor : Party) (seeded : 0 < item.before.stock actor .seed) :
    0 < (law.step item.before item.request).stock actor .seed := by
  by_cases inside : actor ∈ actors count
  · exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked item member) actor inside) seeded
  · have zero := (every_actual_cut_has_complete_inventory count item member actor inside .seed).1
    rw [zero] at seeded
    exact False.elim (lt_irrefl _ seeded)

theorem actual_prefix_keeps_seeded_addresses : seedCheck 19 = true := by
  decide +kernel

theorem every_earlier_prefix_keeps_seeded_addresses (count : Nat) (within : count ≤ 19)
    (item : ExecutionItem Party Good Port Technology Unit) (member : item ∈ Feedback.receipts count)
    (actor : Party) (seeded : 0 < item.before.stock actor .seed) :
    0 < (law.step item.before item.request).stock actor .seed := by
  obtain ⟨ordinal, before, inside⟩ := List.mem_flatMap.mp member
  exact checked_seeds_persist_for_every_address 19 actual_prefix_keeps_seeded_addresses item
    (receipt_member 19 ordinal (by have := List.mem_range.mp before; omega) item inside) actor seeded

private theorem execution_keeps_positive_seed (current : Current)
    (word : RawEvent Party Good Port Technology Unit) (index : Nat) (actor : Party)
    (seeded : 0 < current.stock actor .seed)
    (kept : ∀ item ∈ (law.execute current index word).items,
      0 < item.before.stock actor .seed → 0 < (law.step item.before item.request).stock actor .seed) :
    0 < (law.execute current index word).final.stock actor .seed := by
  induction word generalizing current index with
  | nil => exact seeded
  | cons request rest ih =>
      apply ih (law.step current request) (index + 1)
      · exact kept ⟨index, current, request⟩ (by simp [RawLaw.execute]) seeded
      · intro item inside
        exact kept item (List.mem_cons_of_mem _ inside)

theorem actual_seeded_bearer_survives_later_frames (start later : Nat) (within : start + later ≤ 19)
    (actor : Party) (seeded : 0 < (source.currentAt start).stock actor .seed) :
    0 < (source.currentAt (start + later)).stock actor .seed := by
  simp only [raw_current_frame] at seeded ⊢
  induction later with
  | zero => exact seeded
  | succ later ih =>
      exact execution_keeps_positive_seed (source.frameAt (start + later)).raw
        (source.frameWord (start + later) (source.frameAt (start + later))) 0 actor
        (ih (by omega)) (by
          intro item member
          exact checked_seeds_persist_for_every_address 19 actual_prefix_keeps_seeded_addresses item
            (receipt_member 19 (start + later) (by omega) item member) actor)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit
