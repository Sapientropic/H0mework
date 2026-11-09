import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material.Receipt
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.Conservation
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation Reparation.Actual Reparation.Actual.Allocation
open scoped BigOperators

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Community]

variable {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

local notation "Row" => Occurrence seed community × Balance
local notation "Pos" => Position seed past input
local notation "Damage" => Boundary.Actual.DamageAt (endAt seed past) input community

private theorem a_positive_allocation_has_an_original_cross_community_receipt
    (position : Pos) (good : Good) {rows : List Row}
    (changes : Changes rows) (uses : changes.uses (itemOffer seed past input position))
    (positive : 0 < changes.assignedForGood good) :
    ∃ row : Row, row.1.key.2.2 = good ∧ 0 < receiptCredit seed.native.input.law
      (originalItem seed past input position) row.1.key := by
  induction changes with
  | nil => exact (lt_irrefl _ positive).elim
  | @cons row _ first later inherited =>
    have shares : first.uses (itemOffer seed past input position) ∧ later.uses (itemOffer seed past input position) := uses
    cases first with
    | keep =>
      exact inherited shares.2 (by simpa only [Changes.assignedWhere, Change.amount, ite_self, zero_add] using positive)
    | pay share _ =>
      by_cases atGood : row.1.key.2.2 = good
      · refine ⟨row, atGood, ?_⟩
        have offered : itemOffer seed past input position row.1.key = some share.receipt := shares.1
        rw [← item_offer_is_the_actual_signed_credit, Offer.quantity, offered]
        exact share.receipt.positive
      · exact inherited shares.2 (by simpa only [Changes.assignedWhere, if_neg atGood, zero_add] using positive)

private def lossFor (good : Good) (damage : Damage) : ℚ :=
  if damage.key.2.2 = good then damage.quantity else 0

private theorem lossFor_nonnegative (good : Good) (damage : Damage) :
    0 ≤ lossFor past input good damage := by
  unfold lossFor
  split
  · exact damage.positive.le
  · exact le_rfl

private def filed (good : Good) (position : Pos) : ℚ :=
  ∑ damage ∈ ((Boundary.Actual.damages (endAt seed past) input community).toFinset.filter
    (fun damage => damage.position = position)), lossFor past input good damage

private theorem the_new_loss_at_an_item_covers_its_allocated_payments
    (position : Pos) (rows : List Row) (good : Good) :
    (atItem seed past input position rows).changes.assignedForGood good ≤ filed (community := community) past input good position := by
  let plan := atItem seed past input position rows
  by_cases positive : 0 < plan.changes.assignedForGood good
  · obtain ⟨row, exactGood, paid⟩ := a_positive_allocation_has_an_original_cross_community_receipt
      past input position good plan.changes plan.original positive
    let receipt : SignedReceipt seed row.1.key := ⟨past, input, position, paid⟩
    obtain ⟨damage, atPosition, key, amount⟩ := every_cross_community_receipt_opens_its_equal_reverse_damage
      receipt row.1.damage.actual_foreign_debit.1.1
    have checked := positive_receipt_has_the_original_signature_and_delivery _ _ _ paid
    obtain ⟨goods, operation, _⟩ := checked.2.2
    have bound := one_material_good_cannot_be_spent_twice past input position rows good
    rw [unitQuantity, operation] at bound
    change plan.changes.assignedForGood good ≤ receiptCredit seed.native.input.law
      (originalItem seed past input position) (row.1.key.1, row.1.key.2.1, good) at bound
    have address : (row.1.key.1, row.1.key.2.1, good) = row.1.key := by
      rw [← exactGood]
    rw [address] at bound
    have measured : lossFor past input good damage = receipt.quantity := by
      unfold lossFor
      have sameGood : damage.key.2.2 = good := (congrArg (fun key : Key Party Good => key.2.2) key).trans exactGood
      rw [if_pos sameGood, amount]
    have listed : damage ∈ ((Boundary.Actual.damages (endAt seed past) input community).toFinset.filter
        (fun damage => damage.position = position)) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (Boundary.Actual.every_actual_debit_is_assessed damage), atPosition⟩
    have mass : lossFor past input good damage ≤ filed (community := community) past input good position := by
      unfold filed
      exact Finset.single_le_sum (fun item _ => lossFor_nonnegative past input good item) listed
    rw [measured] at mass
    exact bound.trans mass
  · apply (le_of_not_gt positive).trans
    unfold filed
    exact Finset.sum_nonneg (fun damage _ => lossFor_nonnegative past input good damage)

private theorem original_position_fold_bounds_allocations
    {positions : List Pos} {rows : List Row} (trace : ItemWrites past input positions rows) (good : Good) :
    trace.assignedForGood good ≤ (positions.map (filed (community := community) past input good)).sum := by
  induction trace with
  | nil => exact le_rfl
  | @next position _ rows _ prior =>
    exact add_le_add (the_new_loss_at_an_item_covers_its_allocated_payments past input position rows good) prior

private theorem the_filed_positions_sum_to_the_actual_new_loss (good : Good) :
    ((itemPositions (seed := seed) past input).map (filed (community := community) past input good)).sum =
      ((openings seed community past input).map fun loss => if loss.key.2.2 = good then loss.quantity else 0).sum := by
  let losses := Boundary.Actual.damages (endAt seed past) input community
  have distinct : losses.Nodup := Boundary.Actual.each_damage_address_occurs_once _ _ _
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  change (∑ position : Pos, ∑ damage ∈ losses.toFinset.filter (fun damage => damage.position = position),
    lossFor past input good damage) = _
  rw [Finset.sum_fiberwise losses.toFinset (fun damage => damage.position)]
  unfold openings
  rw [List.map_map]
  exact List.sum_toFinset _ distinct

/-- Under the original single-signer receipt rule, even accepting
further attacks cannot decrease total cross-community liability. -/
theorem every_original_tick_keeps_or_increases_outstanding_reparation
    (state : State seed community past) (good : Good) :
    outstandingForGood good state.stack.balances ≤ outstandingForGood good (advance state input).stack.balances := by
  let trace := atInput past input (posted state input).stack.balances
  have capped := (original_position_fold_bounds_allocations past input trace good).trans
    (the_filed_positions_sum_to_the_actual_new_loss (seed := seed) (community := community) past input good).le
  have accounted := trace.outstanding_and_assigned_eq_before good
  have written := (the_same_input_carries_its_whole_write_and_cannot_reuse_a_receipt state input good).2.1
  have opened : outstandingForGood good (posted state input).stack.balances =
      outstandingForGood good state.stack.balances +
        ((openings seed community past input).map fun loss => if loss.key.2.2 = good then loss.quantity else 0).sum := by
    rw [posted_balances]
    simp only [outstandingWhere, List.map_append, List.sum_append, List.map_map, Function.comp_def, opening]
  change outstandingForGood good trace.result + trace.assignedForGood good =
    outstandingForGood good (posted state input).stack.balances at accounted
  rw [written]
  change _ ≤ outstandingForGood good trace.result
  linarith only [accounted, opened, capped]

theorem every_original_history_keeps_or_increases_outstanding_reparation
    (tail : Reparation.Actual.Script Party Good Port Technology Instrument) (good : Good) :
    outstandingForGood good (run seed community past).stack.balances ≤
      outstandingForGood good (run seed community (past ++ tail)).stack.balances := by
  induction tail using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton front attempt prior =>
    rw [← List.append_assoc, run_snoc]
    exact prior.trans (every_original_tick_keeps_or_increases_outstanding_reparation _ _ _ good)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Material
