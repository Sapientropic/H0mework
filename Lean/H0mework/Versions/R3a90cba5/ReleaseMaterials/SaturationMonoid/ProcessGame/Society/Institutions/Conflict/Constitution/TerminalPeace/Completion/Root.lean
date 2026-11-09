import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion.History

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion

open Capitalism.Universal.Abolition.Material (ActualAndIndependent)
open Renewal

noncomputable section

structure PeaceTail (policy : Interleaving anchor) (tail : Nat → Visit anchor) : Prop where
  starts : tail 0 = policy.start peace
  ledgerAndNext : ∀ n, policy.nextWholeWrite (tail n) = (tail (n + 1)).ready.val.state.resident.erase
  originalReparation : ∀ n, (tail n).ready.val.state.stack.balances = [(Original.occurrence, Settlement.clearedBalance)]
  originalPrincipal : ∀ n, (tail n).ready.val.native.raw.claims () true false = 6
  noActualDamage : ∀ n, NoNewDamage (tail n).ready.val
  firstPaid : ∀ person, foodPaid (tail 0).ready.val.items person = 1
  everyElapsedHourPaid : ∀ n, (tail n).ready.val.native.raw.clock < (tail (n + 1)).ready.val.native.raw.clock →
    ∀ person, 1 ≤ foodPaid (tail (n + 1)).ready.val.items person
  independentExit : ∀ n person,
    ActualAndIndependent Supply.revisedInput (tail n).ready.val.native.raw (Supply.personalWord person)
  independentItemExit : ∀ n, ItemExits (tail n).ready.val.items
  noSkippedHour : ∀ n,
    (tail (n + 1)).ready.val.native.raw.clock = (tail n).ready.val.native.raw.clock ∨
    (tail (n + 1)).ready.val.native.raw.clock = (tail n).ready.val.native.raw.clock + 1
  dueFromEachCut : ∀ n, (tail n).ready.val.native.raw.clock + 1 ≤
    (tail (n + (tail n).pending + 1)).ready.val.native.raw.clock
  clockCofinal : ∀ cut bound, ∃ n ≥ cut, bound < (tail n).ready.val.native.raw.clock

/-- Even a refusal visit at the same clock reads the payment made at
that hour's actual opening. Only the opening's items are counted. -/
theorem PeaceTail.each_cut_has_an_actual_paid_hour {policy : Interleaving anchor} {tail : Nat → Visit anchor}
    (safe : PeaceTail policy tail) (cut : Nat) :
    ∃ paid ≤ cut, (tail paid).ready.val.native.raw.clock = (tail cut).ready.val.native.raw.clock ∧
      ∀ person, 1 ≤ foodPaid (tail paid).ready.val.items person := by
  induction cut with
  | zero => exact ⟨0, le_rfl, rfl, fun person => (safe.firstPaid person).ge⟩
  | succ n earlier =>
    rcases safe.noSkippedHour n with same | later
    · obtain ⟨paid, before, clock, paidItems⟩ := earlier
      exact ⟨paid, Nat.le.step before, clock.trans same.symm, paidItems⟩
    · have elapsed : (tail n).ready.val.native.raw.clock < (tail (n + 1)).ready.val.native.raw.clock := by
        rw [later]
        exact lt_add_of_pos_right _ zero_lt_one
      exact ⟨n + 1, le_rfl, rfl, safe.everyElapsedHourPaid n elapsed⟩

theorem the_original_compiler_generates_a_paid_peace_tail (policy : Interleaving anchor) :
    PeaceTail policy (policy.run peace) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, the_first_peace_write_pays_each_person, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact policy.next_is_the_whole_successor_of_the_original_visit (policy.run peace n)
  · intro n
    exact (policy.every_run_retains_its_original_balances peace n).trans
      the_first_peace_write_clears_the_original_loss_but_keeps_its_address
  · intro n
    rw [policy.every_run_retains_its_material_principal peace n, the_first_peace_write_reads_the_paid_current]
    rfl
  · intro n
    cases n with
    | zero => exact the_first_peace_write_has_no_new_damage
    | succ n => exact policy.next_has_no_damage (policy.run peace n)
  · intro n
    exact policy.next_pays_at_each_hour (policy.run peace n)
  · intro n person
    exact every_cut_has_a_personal_exit (policy.run peace n).ready person
  · intro n
    cases n with
    | zero => exact the_first_peace_write_keeps_each_item_exit
    | succ n => exact policy.next_keeps_every_item_exit (policy.run peace n)
  · intro n
    exact policy.next_has_its_original_clock_cell (policy.run peace n)
  · intro n
    rw [Nat.add_assoc]
    unfold Interleaving.run
    rw [policy.runFrom_add]
    exact policy.the_due_service_cannot_be_delayed_past_the_pending_queue (policy.run peace n)
  · exact policy.every_run_is_clock_cofinal_after_every_cut peace

def ResponsibilityPreservingTerminal : Prop :=
  ∀ policy : Interleaving anchor,
    Nonempty (ActualRun policy) ∧ ∀ actual : ActualRun policy,
      (actual.atVisit 4).whole = peace.val.state.resident.erase ∧
      ∃! tail, FactorsThroughPeace policy actual tail ∧ PeaceTail policy tail

theorem the_paid_peace_world_is_responsibility_preserving_terminal :
    ResponsibilityPreservingTerminal := by
  intro policy
  refine ⟨⟨realize policy⟩, fun actual => ⟨(every_actual_run_passes_the_same_original_whole_writes policy actual).2.2.2.2, ?_⟩⟩
  obtain ⟨tail, factor, unique⟩ := every_actual_future_has_the_unique_living_suffix policy actual
  have sourceFactors : FactorsThroughPeace policy actual (policy.run peace) := by
    intro n
    rw [every_actual_run_is_the_source_run policy actual, the_generated_future_replays_the_original_compiler]
  have exactTail : tail = policy.run peace := (unique _ sourceFactors).symm
  exact ⟨tail, ⟨factor, exactTail.symm ▸ the_original_compiler_generates_a_paid_peace_tail policy⟩,
    fun other holds => unique other holds.1⟩

/-- The original six-unit loss has an actual two-party settlement and
a finite, compulsory entry into an open, paid continuation. The source
provides the first whole write and the unique continuation for each
raw scheduler and arbitration. -/
theorem source_generated_terminal_peace :
    Original.occurrence.quantity = 6 ∧
    (Settlement.jointOffer Settlement.replies Settlement.protectedPast Settlement.payerInput
      Settlement.paidPosition Original.occurrence.key = some Settlement.receiptSix) ∧
    (Boundary.Actual.damages Settlement.physicalCut Settlement.payerInput Original.community = []) ∧
    (peace.val.state.stack.balances = [(Original.occurrence, Settlement.clearedBalance)]) ∧
    Settlement.clearedBalance.remaining = 0 ∧
    Settlement.physicalCut.raw.clock = 4 ∧ peace.val.native.raw.clock = 5 ∧
    ResponsibilityPreservingTerminal :=
  ⟨Original.loss_six, Settlement.the_same_position_issues_the_actual_joint_receipt,
    Settlement.the_protected_payment_creates_no_damage,
    the_first_peace_write_clears_the_original_loss_but_keeps_its_address, rfl,
    congrArg (fun raw : Original.Raw => raw.clock) Settlement.protected_stock,
    congrArg (fun raw : Original.Raw => raw.clock) the_first_peace_write_reads_the_paid_current,
    the_paid_peace_world_is_responsibility_preserving_terminal⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Completion
