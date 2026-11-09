import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Interleave
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Interleaving

noncomputable section

variable {history : Original.Word} (policy : Interleaving history)

theorem next_clock_mono (prior : Visit history) :
    prior.ready.val.native.raw.clock ≤ (policy.next prior).ready.val.native.raw.clock := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active, renew_raw]
    exact le_add_of_nonneg_right zero_le_one
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1]
    exact dispatch_never_rolls_back_the_original_clock _ _

/-- Pending counts already queued ordinary writes. It is a bound in
actual visits until the next paid hour, regardless of those replies. -/
theorem the_due_service_cannot_be_delayed_past_the_pending_queue (origin : Visit history) :
    origin.ready.val.native.raw.clock + 1 ≤
      (policy.runFrom origin (origin.pending + 1)).ready.val.native.raw.clock := by
  generalize queue : origin.pending = length
  induction length generalizing origin with
  | zero =>
    change origin.ready.val.native.raw.clock + 1 ≤ (policy.next origin).ready.val.native.raw.clock
    rw [next_at_service _ _ queue, renew_raw]
  | succ length earlier =>
    have remaining := (next_at_queue policy origin length queue).2
    have forward := earlier (policy.next origin) remaining
    rw [show length + 1 + 1 = 1 + (length + 1) by omega, runFrom_add]
    exact (add_le_add_left (next_clock_mono policy origin) 1).trans forward

theorem runFrom_clock_mono (origin : Visit history) (n : Nat) :
    origin.ready.val.native.raw.clock ≤ (policy.runFrom origin n).ready.val.native.raw.clock := by
  induction n with
  | zero => exact le_rfl
  | succ n before => exact before.trans (next_clock_mono policy (policy.runFrom origin n))

theorem the_first_crossing_of_each_open_hour_is_paid (origin : Visit history) :
    ∃ last < origin.pending + 1,
      (policy.runFrom origin last).ready.val.native.raw.clock = origin.ready.val.native.raw.clock ∧
      (policy.runFrom origin (last + 1)).ready.val.native.raw.clock = origin.ready.val.native.raw.clock + 1 ∧
      (∀ earlier ≤ last,
        (policy.runFrom origin earlier).ready.val.native.raw.clock = origin.ready.val.native.raw.clock) ∧
      ∀ person, 1 ≤ foodPaid (policy.runFrom origin (last + 1)).ready.val.items person := by
  let crossed (n : Nat) := origin.ready.val.native.raw.clock < (policy.runFrom origin n).ready.val.native.raw.clock
  have due := (lt_add_of_pos_right origin.ready.val.native.raw.clock zero_lt_one).trans_le
    (the_due_service_cannot_be_delayed_past_the_pending_queue policy origin)
  have reachable : ∃ n, crossed n := ⟨origin.pending + 1, due⟩
  have limit : Nat.find reachable ≤ origin.pending + 1 := Nat.find_min' reachable due
  have reached := Nat.find_spec reachable
  cases atFirst : Nat.find reachable with
  | zero =>
    rw [atFirst] at reached
    exact (lt_irrefl origin.ready.val.native.raw.clock reached).elim
  | succ last =>
    have before (earlier : Nat) (early : earlier ≤ last) :
        (policy.runFrom origin earlier).ready.val.native.raw.clock = origin.ready.val.native.raw.clock := by
      have missed : ¬ crossed earlier := Nat.find_min reachable (by rw [atFirst]; omega)
      exact le_antisymm (le_of_not_gt missed) (runFrom_clock_mono policy origin earlier)
    let prior := policy.runFrom origin last
    have elapsed : prior.ready.val.native.raw.clock < (policy.next prior).ready.val.native.raw.clock := by
      change (policy.runFrom origin last).ready.val.native.raw.clock <
        (policy.runFrom origin (last + 1)).ready.val.native.raw.clock
      rw [before last le_rfl]
      rw [atFirst] at reached
      exact reached
    refine ⟨last, by omega, before last le_rfl, ?_, before, ?_⟩
    · change (policy.next prior).ready.val.native.raw.clock = _
      rcases policy.next_has_its_original_clock_cell prior with same | later
      · exact ((ne_of_lt elapsed) same.symm).elim
      · exact later.trans (congrArg (· + 1) (before last le_rfl))
    · exact policy.next_pays_at_each_hour prior elapsed

theorem the_original_clock_is_cofinal_from_each_actual_visit (origin : Visit history) (bound : ℚ) :
    ∃ visits, bound < (policy.runFrom origin visits).ready.val.native.raw.clock := by
  have crosses : ∀ periods : ℕ, ∃ visits, origin.ready.val.native.raw.clock + periods ≤
      (policy.runFrom origin visits).ready.val.native.raw.clock := by
    intro periods
    induction periods with
    | zero => exact ⟨0, by simp [runFrom]⟩
    | succ periods earlier =>
      obtain ⟨visits, paid⟩ := earlier
      let cut := policy.runFrom origin visits
      refine ⟨visits + (cut.pending + 1), ?_⟩
      rw [runFrom_add, Nat.cast_succ, ← add_assoc]
      exact (add_le_add_left paid 1).trans (the_due_service_cannot_be_delayed_past_the_pending_queue policy cut)
  obtain ⟨periods, further⟩ := exists_nat_gt (bound - origin.ready.val.native.raw.clock)
  obtain ⟨visits, paid⟩ := crosses periods
  exact ⟨visits, (by linarith : bound < origin.ready.val.native.raw.clock + periods).trans_le paid⟩

theorem every_run_is_clock_cofinal_after_every_cut (origin : Ready history) (cut : Nat) (bound : ℚ) :
    ∃ visits ≥ cut, bound < (policy.run origin visits).ready.val.native.raw.clock := by
  obtain ⟨extra, later⟩ := the_original_clock_is_cofinal_from_each_actual_visit policy (policy.run origin cut) bound
  refine ⟨cut + extra, Nat.le_add_right _ _, ?_⟩
  unfold run
  rw [runFrom_add]
  exact later

theorem every_run_retains_its_original_balances (origin : Ready history) (visits : Nat) :
    (policy.run origin visits).ready.val.state.stack.balances = origin.val.state.stack.balances := by
  induction visits with
  | zero => rfl
  | succ visits kept =>
    exact (next_keeps_original_balances policy (policy.run origin visits)).trans kept

theorem every_run_retains_its_material_principal (origin : Ready history) (visits : Nat) :
    (policy.run origin visits).ready.val.native.raw.claims = origin.val.native.raw.claims := by
  induction visits with
  | zero => rfl
  | succ visits kept =>
    exact (next_keeps_material_principal policy (policy.run origin visits)).trans kept

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Interleaving
