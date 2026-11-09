import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Ledger
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Balance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Execution (endAt endAt_append)
open Reparation.Actual
open Occurrence.Unbounded.Nonattainment (loss)
open External.Countermodel (CycleAt cycle nextPast nextPast_eq advanceCycle levyOccurrence
  the_real_cycle_restores_its_original_material_state the_cycle_writes_exactly_one_new_unpaid_row
  the_levy_opens_exactly_its_original_loss the_new_levy_has_its_exact_position the_new_levy_writes_six
  original_levy_items original_levy_drain middle_raw)
open private levy_trace from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original.Cut
open private prior_has_no_loss from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Original
open private no_charge_without_original_signatures from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Ledger
open private after_levy middle_review from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.External.Countermodel.Cycle

noncomputable section

/-- Before the first levy the original ledger has no such debt. The raw
return in each following cycle has no joint receipt, so the prior rows stay due. -/
def beforeLevy : Nat → Original.Word
  | 0 => Original.prior
  | n + 1 => nextPast (beforeLevy n)

private theorem cycleAt : ∀ n, CycleAt (endAt Original.seed (beforeLevy n))
  | 0 => by
    have ready := levy_trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp)
    exact ⟨Original.prior_source, Original.before_raw, ready.1, ready.2⟩
  | n + 1 => by
    change CycleAt (endAt Original.seed (nextPast (beforeLevy n)))
    rw [nextPast_eq, endAt_append]
    exact the_real_cycle_restores_its_original_material_state (cycleAt n)

def indexedLoss (n : Nat) := levyOccurrence (beforeLevy n) (cycleAt n)

abbrev birth (n : Nat) := Occurrence.history (indexedLoss n)
abbrev accounted (n : Nat) := birth n ++ [none]

private theorem beforeLevy_length (n : Nat) : (beforeLevy n).length = 2 + 4 * n := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    change (nextPast (beforeLevy n)).length = _
    rw [nextPast_eq, List.length_append, earlier]
    change 2 + 4 * n + 4 = 2 + 4 * (n + 1)
    omega

theorem indexed_address (n : Nat) : (indexedLoss n).address = (2 + 4 * n, 0, (false, true, false)) := by
  rw [indexedLoss, the_new_levy_has_its_exact_position, beforeLevy_length]

theorem the_actual_origins_are_pairwise_distinct : Function.Injective indexedLoss := by
  intro first last same
  have index := congrArg (fun origin : Reparation.Actual.Occurrence Original.seed Original.community => origin.address.1) same
  rw [indexed_address, indexed_address] at index
  omega

private abbrev oldRows (n : Nat) := (Reparation.Actual.run Original.seed Original.community (beforeLevy n)).stack.balances
private abbrev newRow (n : Nat) := (indexedLoss n, Reparation.Actual.opening (indexedLoss n))

private theorem after_cycle_rows (n : Nat) (victims : ∀ row ∈ oldRows n, row.1.key.1 = false) :
    oldRows (n + 1) = oldRows n ++ [newRow n] := by
  change (Reparation.Actual.run Original.seed Original.community
    ((((beforeLevy n ++ [Original.attack]) ++ [none]) ++ [External.Countermodel.returned]) ++ [none])).stack.balances = _
  rw [Reparation.Actual.run_snoc, Reparation.Actual.run_snoc, Reparation.Actual.run_snoc, Reparation.Actual.run_snoc]
  exact the_cycle_writes_exactly_one_new_unpaid_row (Reparation.Actual.run Original.seed Original.community (beforeLevy n))
    (cycleAt n) victims

private theorem due_after_new_row (n : Nat) : Settlement.outstanding false (oldRows n ++ [newRow n]) =
    Settlement.outstanding false (oldRows n) + 6 := by
  unfold Settlement.outstanding
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    show (indexedLoss n).key.2.2 = false from rfl, if_true]
  exact congrArg ((Settlement.outstanding false (oldRows n)) + ·) (the_new_levy_writes_six (beforeLevy n) (cycleAt n))

private theorem older (n : Nat) : (beforeLevy n).IsPrefix (beforeLevy (n + 1)) := by
  change (beforeLevy n).IsPrefix (nextPast (beforeLevy n))
  rw [nextPast_eq]
  exact List.prefix_append _ _

private theorem born_before_next (n : Nat) : (birth n).IsPrefix (beforeLevy (n + 1)) := by
  change (beforeLevy n ++ [Original.attack]).IsPrefix
    ((((beforeLevy n ++ [Original.attack]) ++ [none]) ++ [External.Countermodel.returned]) ++ [none])
  exact ((List.prefix_append _ _).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)

private theorem earlier_rows (n : Nat) :
    (∀ row ∈ oldRows n, row.1.key = loss.key ∧ (Occurrence.history row.1).IsPrefix (beforeLevy n)) ∧
    Settlement.outstanding false (oldRows n) = 6 * (n : ℚ) := by
  induction n with
  | zero =>
    change (_ ∧ Settlement.outstanding false (Reparation.Actual.run Original.seed Original.community Original.prior).stack.balances = _)
    change (∀ row ∈ (Reparation.Actual.run Original.seed Original.community Original.prior).stack.balances,
      row.1.key = loss.key ∧ (Occurrence.history row.1).IsPrefix Original.prior) ∧ _
    rw [prior_has_no_loss]
    simp [Settlement.outstanding]
  | succ n earlier =>
    have victims : ∀ row ∈ oldRows n, row.1.key.1 = false := by
      intro row present
      rw [(earlier.1 row present).1]
      rfl
    rw [after_cycle_rows n victims]
    refine ⟨?_, ?_⟩
    · intro row listed
      rcases List.mem_append.mp listed with old | recent
      · exact ⟨(earlier.1 row old).1, (earlier.1 row old).2.trans (older n)⟩
      · rcases List.mem_singleton.mp recent with rfl
        exact ⟨rfl, born_before_next n⟩
    · rw [due_after_new_row, earlier.2, Nat.cast_succ]
      ring

private theorem birth_rows (n : Nat) : (Occurrence.originState (indexedLoss n)).stack.balances = oldRows n ++ [newRow n] := by
  have victims : ∀ row ∈ oldRows n ++ [newRow n], row.1.key.1 = false := by
    intro row listed
    rcases List.mem_append.mp listed with old | recent
    · rw [((earlier_rows n).1 row old).1]
      rfl
    · rcases List.mem_singleton.mp recent with rfl
      rfl
  change (Reparation.Actual.run Original.seed Original.community (beforeLevy n ++ [Original.attack])).stack.balances = _
  rw [Reparation.Actual.run_snoc]
  have kept := no_charge_without_original_signatures (Reparation.Actual.run Original.seed Original.community (beforeLevy n))
    Original.attack _ (original_levy_items (cycleAt n)) rfl (by
      rw [the_levy_opens_exactly_its_original_loss (beforeLevy n) (cycleAt n)]
      exact victims)
  rw [the_levy_opens_exactly_its_original_loss (beforeLevy n) (cycleAt n)] at kept
  exact kept

theorem native_head_is_empty (n : Nat) : Boundary.Actual.items (endAt Original.seed (birth n)) none = [] := by
  change Boundary.Actual.items (endAt Original.seed (beforeLevy n ++ [Original.attack])) none = []
  rw [endAt_append]
  exact original_levy_drain (cycleAt n)

theorem actual_accounted_cut (n : Nat) : (endAt Original.seed (accounted n)).raw = Snapshot 0 ∧
    Ready (endAt Original.seed (accounted n)) ∧ ReviewAvailable (endAt Original.seed (accounted n)) := by
  have real : endAt Original.seed (accounted n) = External.Countermodel.middle (endAt Original.seed (beforeLevy n)) := by
    change endAt Original.seed ((beforeLevy n ++ [Original.attack]) ++ [none]) = _
    rw [List.append_assoc, endAt_append]
    rfl
  rw [real]
  refine ⟨?_, (after_levy (cycleAt n)).1, middle_review (cycleAt n)⟩
  rw [middle_raw (cycleAt n)]
  norm_num [Snapshot]

private theorem accounted_rows (n : Nat) :
    (Occurrence.reached replies (indexedLoss n) [none]).stack.balances = oldRows n ++ [newRow n] := by
  change (Occurrence.writeAfter replies (Occurrence.originState (indexedLoss n)) ([] ++ [none])).stack.balances = _
  rw [Occurrence.writeAfter_snoc_balances]
  have empty : Boundary.Actual.items (endAt Original.seed (birth n ++ [])) none = [] := by
    simpa only [List.append_nil] using native_head_is_empty n
  rw [a_native_accounting_input_keeps_the_entire_balance_table _ _ empty, Occurrence.writeAfter_nil_balances]
  exact birth_rows n

theorem the_original_portfolio_is_all_due (n : Nat) :
    let rows := (Occurrence.reached replies (indexedLoss n) [none]).stack.balances
    (∀ row ∈ rows, row.1.key = loss.key ∧ (Occurrence.history row.1).IsPrefix (accounted n)) ∧
      Settlement.outstanding false rows = 6 * ((n : ℚ) + 1) := by
  dsimp only
  rw [accounted_rows n]
  refine ⟨?_, ?_⟩
  · intro row listed
    rcases List.mem_append.mp listed with old | recent
    · have origin := (earlier_rows n).1 row old
      have current : (beforeLevy n).IsPrefix (accounted n) :=
        (List.prefix_append (beforeLevy n) [Original.attack]).trans (List.prefix_append _ _)
      exact ⟨origin.1, origin.2.trans current⟩
    · rcases List.mem_singleton.mp recent with rfl
      exact ⟨rfl, List.prefix_append _ _⟩
  · rw [due_after_new_row, (earlier_rows n).2]
    ring

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated
