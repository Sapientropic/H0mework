import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Consumers.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.FIFO
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.History

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation.Consumers

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (primitiveScript)
open Reparation.Consumers (warCut address receipt)

noncomputable section

abbrev older := (firstOrigin, opening firstOrigin)
abbrev younger := (secondOrigin, opening secondOrigin)
abbrev oldRows := [older, younger]
abbrev offer := itemOffer warCut (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition

private theorem older_can_receive : later firstOrigin signedReceipt := by
  left
  change (primitiveScript beforeFirst ++ [tick (levyOf 2)]).IsPrefix (primitiveScript beforeReceipt)
  refine ⟨none :: primitiveScript [levyOf 4], ?_⟩
  simp only [beforeReceipt, beforeSecond, Quantities.Execution.primitiveScript_append,
    primitiveScript, List.append_assoc]
  rfl

private theorem younger_can_receive : later secondOrigin signedReceipt := by
  left
  change (primitiveScript beforeSecond ++ [tick (levyOf 4)]).IsPrefix (primitiveScript beforeReceipt)
  refine ⟨[none], ?_⟩
  simp only [beforeReceipt, Quantities.Execution.primitiveScript_append, primitiveScript,
    List.append_assoc]
  rfl

private theorem actual_offer : offer address = some signedReceipt := by
  have positive : 0 < receiptCredit warCut.native.input.law
      (originalItem warCut (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition) address := by
    rw [the_original_signed_receipt_is_three]
    decide +kernel
  unfold offer itemOffer
  exact dif_pos positive

private theorem older_due : eligible offer older = 2 := by
  have supplied : offer older.1.key = some signedReceipt := actual_offer
  have allowed : later older.1 signedReceipt := older_can_receive
  unfold eligible
  rw [supplied]
  exact (if_pos allowed).trans first_original_quantity

private theorem younger_due : eligible offer younger = 4 := by
  have supplied : offer younger.1.key = some signedReceipt := actual_offer
  have allowed : later younger.1 signedReceipt := younger_can_receive
  unfold eligible
  rw [supplied]
  exact (if_pos allowed).trans second_original_quantity

private theorem original_available : offer.quantity address = 3 :=
  (item_offer_is_the_actual_signed_credit warCut _ _ _ _).trans the_original_signed_receipt_is_three

private theorem older_prefix : demand offer address [older] = 2 := by
  have key : firstOrigin.key = address := rfl
  simp only [demand, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_pos key, older_due, add_zero]

def splitPlan : Plan offer oldRows :=
  atItem warCut (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition oldRows

def olderMove : Change firstOrigin (opening firstOrigin) := splitPlan.changes.head

def youngerMove : Change secondOrigin (opening secondOrigin) :=
  (Changes.split [older] [younger] splitPlan.changes).2.head

theorem the_actual_three_units_pay_two_then_one :
    olderMove.amount = 2 ∧ youngerMove.amount = 1 := by
  have first := original_position_has_exact_FIFO_payment offer (Capacity.full offer) [] older [younger]
  have second := original_position_has_exact_FIFO_payment offer (Capacity.full offer) [older] younger []
  change olderMove.amount = min (max 0 (offer.quantity address - 0)) (eligible offer older) at first
  change youngerMove.amount = min (max 0 (offer.quantity address - demand offer address [older]))
    (eligible offer younger) at second
  rw [original_available, older_due] at first
  rw [original_available, older_prefix, younger_due] at second
  exact ⟨first.trans (by decide +kernel), second.trans (by decide +kernel)⟩

theorem the_original_two_rows_end_at_zero_and_three :
    olderMove.after.remaining = 0 ∧ youngerMove.after.remaining = 3 := by
  obtain ⟨first, second⟩ := the_actual_three_units_pay_two_then_one
  constructor
  · rw [Change.after_exact, first]
    change firstOrigin.quantity - 2 = 0
    rw [first_original_quantity, sub_self]
  · rw [Change.after_exact, second]
    change secondOrigin.quantity - 1 = 3
    rw [second_original_quantity]
    decide +kernel

theorem the_joint_result_retains_both_rows_with_the_actual_amounts :
    (splitPlan.changes.result.map (fun row => row.2.remaining)) = [0, 3] := by
  obtain ⟨first, second⟩ := the_original_two_rows_end_at_zero_and_three
  change splitPlan.changes.head.after.remaining = 0 at first
  change (Changes.split [older] [younger] splitPlan.changes).2.head.after.remaining = 3 at second
  generalize computed : splitPlan.changes = moves at first second ⊢
  cases moves with
  | cons olderMove tail =>
    cases tail with
    | cons youngerMove rest =>
      cases rest
      change olderMove.after.remaining = 0 at first
      change youngerMove.after.remaining = 3 at second
      change [olderMove.after.remaining, youngerMove.after.remaining] = [0, 3]
      rw [first, second]

theorem the_same_three_unit_delivery_is_charged_once :
    splitPlan.changes.assignedFor address = 3 ∧ (splitPlan.remainder.balance address).remaining = 0 := by
  have keyFirst : firstOrigin.key = address := rfl
  have keySecond : secondOrigin.key = address := rfl
  have demandExact : demand offer address oldRows = 6 := by
    simp only [demand, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, if_pos keyFirst,
      if_pos keySecond, older_due, younger_due, add_zero]
    decide +kernel
  have exactAllocation := each_item_attains_the_original_joint_capacity
    (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition oldRows address
  change splitPlan.changes.assignedFor address =
    min (receiptCredit warCut.native.input.law
      (originalItem warCut (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition) address)
      (demand offer address oldRows) at exactAllocation
  rw [the_original_signed_receipt_is_three, demandExact] at exactAllocation
  have assigned : splitPlan.changes.assignedFor address = 3 := exactAllocation.trans (by decide +kernel)
  have conserved := each_item_conserves_the_original_delivery
    (primitiveScript beforeReceipt) (tick (receipt 3)) receiptPosition oldRows address
  change (splitPlan.remainder.balance address).remaining + splitPlan.changes.assignedFor address = _ at conserved
  rw [assigned, the_original_signed_receipt_is_three] at conserved
  exact ⟨assigned, add_right_cancel (conserved.trans (zero_add _).symm)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation.Consumers
