import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Schedule

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Reparation.Actual Reparation.Actual.Allocation
open ExposureGuard (stop)

noncomputable section

private theorem the_anchor_has_the_original_full_history :
    Settlement.settledHistory = Original.history ++ [stop, Settlement.payerInput, none] := by
  have stopped : protectedCut.history = Original.history ++ [stop] :=
    the_original_installation_writes_its_literal_first_input (fun _ _ _ _ => false)
  unfold Settlement.settledHistory Settlement.protectedPast
  rw [stopped]
  simp only [List.append_assoc]
  rfl

theorem every_visit_retains_the_original_history (tick : Nat) :
    Original.history.IsPrefix (historyAt tick) := by
  apply List.IsPrefix.trans _ (history_extends (Nat.zero_le tick))
  change Original.history.IsPrefix Settlement.settledHistory
  rw [the_anchor_has_the_original_full_history]
  exact List.prefix_append _ _

def roundLoss (n : Nat) : Origin :=
  levyOccurrence (roundPast n) (recurring_cuts_use_the_same_original_material n)

def roundRow (n : Nat) : Row :=
  (roundLoss n, Reparation.Actual.opening (roundLoss n))

theorem the_repeated_levy_opens_at_the_actual_tick (n : Nat) :
    (visitAt (4 * n + 1)).stack.balances.map Prod.fst =
      (roundState n).stack.balances.map Prod.fst ++ [roundLoss n] := by
  have filed : openings Original.seed Original.community (roundPast n) (inputAt (4 * n)) = [roundLoss n] := by
    rw [starts_with_levy]
    exact the_levy_opens_exactly_its_original_loss _ (recurring_cuts_use_the_same_original_material n)
  have written := each_input_keeps_its_old_claims_and_files_exactly_its_new_damage (roundState n) (inputAt (4 * n))
  rw [filed] at written
  exact written

theorem every_new_loss_is_at_its_own_original_address (n : Nat) :
    (roundLoss n).address = (7 + 4 * n, 0, (false, true, false)) := by
  rw [roundLoss, the_new_levy_has_its_exact_position]
  change ((historyAt (4 * n)).length, 0, (false, true, false)) = _
  rw [history_length, the_anchor_has_the_original_full_history]
  rfl

theorem no_repeated_loss_reuses_an_original_address (n : Nat) :
    roundLoss n ≠ Original.occurrence := by
  intro same
  have atAddress := congrArg (fun loss : Origin => loss.address.1) same
  rw [every_new_loss_is_at_its_own_original_address, Original.exact_address] at atAddress
  omega

theorem repeated_losses_have_pairwise_distinct_addresses :
    Function.Injective (fun n => (roundLoss n).address) := by
  intro n m same
  have first := congrArg Prod.fst same
  change (roundLoss n).address.1 = (roundLoss m).address.1 at first
  rw [every_new_loss_is_at_its_own_original_address, every_new_loss_is_at_its_own_original_address] at first
  omega

def newBalances : Nat → List Row
  | 0 => []
  | n + 1 => newBalances n ++ [roundRow n]

private theorem every_new_row_has_the_same_original_victim (n : Nat) :
    ∀ row ∈ newBalances n, row.1.key.1 = false := by
  induction n with
  | zero => exact fun _ absent => (List.not_mem_nil absent).elim
  | succ n earlier =>
    intro row present
    rw [newBalances, List.mem_append, List.mem_singleton] at present
    rcases present with old | rfl
    · exact earlier row old
    · rfl

theorem every_repeated_assault_keeps_the_first_paid_row_and_all_new_rows (n : Nat) :
    (roundState n).stack.balances = (Original.occurrence, Settlement.clearedBalance) :: newBalances n := by
  induction n with
  | zero => exact Settlement.settled_balances
  | succ n earlier =>
    have keepVictims : ∀ row ∈ (roundState n).stack.balances, row.1.key.1 = false := by
      rw [earlier]
      intro row listed
      rcases List.mem_cons.mp listed with rfl | new
      · exact Original.original_victim
      · exact every_new_row_has_the_same_original_victim n row new
    rw [rounds_follow_their_same_whole_account,
      the_cycle_writes_exactly_one_new_unpaid_row _ (recurring_cuts_use_the_same_original_material n) keepVictims]
    rw [earlier, newBalances]
    rfl

theorem each_new_reparation_is_six (n : Nat) : (roundRow n).2.remaining = 6 :=
  the_new_levy_writes_six (roundPast n) (recurring_cuts_use_the_same_original_material n)

private theorem each_new_row_is_retained {earlier later : Nat} (older : earlier < later) :
    roundRow earlier ∈ newBalances later := by
  induction later with
  | zero => omega
  | succ later recurse =>
    rw [newBalances, List.mem_append, List.mem_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp older with prior | rfl
    · exact Or.inl (recurse prior)
    · exact Or.inr rfl

theorem the_cleared_original_row_is_still_visible (n : Nat) :
    ∃ row, (roundState n).read row = .inr (Original.occurrence, Settlement.clearedBalance) := by
  apply (roundState n).every_balance_is_a_row_of_the_current
  rw [every_repeated_assault_keeps_the_first_paid_row_and_all_new_rows]
  exact List.mem_cons_self

theorem every_new_loss_is_visible_at_every_later_cycle {earlier later : Nat} (older : earlier < later) :
    ∃ row, (roundState later).read row = .inr (roundRow earlier) := by
  apply (roundState later).every_balance_is_a_row_of_the_current
  rw [every_repeated_assault_keeps_the_first_paid_row_and_all_new_rows]
  exact List.mem_cons_of_mem _ (each_new_row_is_retained older)

private theorem total_new_reparation (n : Nat) : outstandingForGood false (newBalances n) = 6 * n := by
  induction n with
  | zero => simp [newBalances, outstandingWhere]
  | succ n earlier =>
    have addSix :
        outstandingForGood false (newBalances n ++ [roundRow n]) =
          outstandingForGood false (newBalances n) + 6 := by
      unfold outstandingForGood outstandingWhere
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        show (roundRow n).1.key.2.2 = false from rfl, if_true, add_zero, each_new_reparation_is_six]
    rw [newBalances, addSix, earlier, Nat.cast_succ]
    ring

theorem the_original_root_writes_six_more_unpaid_units_each_cycle (n : Nat) :
    outstandingForGood false (roundState n).stack.balances = 6 * n := by
  rw [every_repeated_assault_keeps_the_first_paid_row_and_all_new_rows]
  have old : Settlement.clearedBalance.remaining = 0 := rfl
  change (if Original.occurrence.key.2.2 = false then Settlement.clearedBalance.remaining else 0) +
    outstandingForGood false (newBalances n) = _
  rw [show Original.occurrence.key.2.2 = false from rfl, if_pos rfl, old, zero_add, total_new_reparation]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel
