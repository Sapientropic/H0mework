import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Unbounded.Nonattainment.Native

/-!
The actual dual-signed writer applies the rational return once to the
original six-unit row. Its residual is computed from the posted portfolio.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Unbounded.Nonattainment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions)

noncomputable section

private theorem opening_portfolio :
    (reached answers loss []).stack.balances = [(loss, Original.balance)] := by
  change (writeAfter answers (originState loss) []).stack.balances = _
  rw [writeAfter_nil_balances]
  exact Original.at_its_birth_the_whole_ledger_opens_six

theorem retain_keeps_six : (balance answers loss []).remaining = 6 := by
  have actual : (loss, Original.balance) ∈ (reached answers loss []).stack.balances := by
    rw [opening_portfolio]
    exact List.mem_singleton_self _
  have same := an_address_has_only_its_original_balance _
    (reached_has_one_row_per_original_address answers loss []) loss
    (balance_is_in_the_reached_rows answers loss []) actual
  exact (congrArg Balance.remaining same).trans Original.balance_six

private theorem accounting_portfolio :
    (reached answers loss [none]).stack.balances = [(loss, Original.balance)] := by
  have absent : itemPositions (seed := Original.seed) (born ++ []) none = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [itemPositions, List.length_finRange, List.append_nil]
    exact congrArg List.length the_native_head_leaves_no_material
  have noDamage : openings Original.seed Original.community (born ++ []) none = [] := by
    rw [List.append_nil]
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ the_native_head_leaves_no_material]
    rfl
  change (writeAfter answers (originState loss) ([] ++ [none])).stack.balances = _
  rw [writeAfter_snoc_balances, Settlement.writeTick_balances, absent, Settlement.writePositions,
    posted_balances, noDamage, List.map_nil, List.append_nil]
  exact opening_portfolio

variable (quantity : ℚ) (positive : 0 < quantity) (small : quantity < 6)

private def jointReceipt : JointReceipt Original.seed loss.key :=
  .mk past (payment quantity) (position quantity positive small) answers rfl rfl (by
    change 0 < payerCredit Original.seed.native.input.law
      (Reparation.Actual.Allocation.originalItem Original.seed past (payment quantity)
        (position quantity positive small)) loss.key
    rwa [the_actual_payer_credit_equals_the_requested_quantity quantity positive small])

private theorem joint_offer :
    Settlement.jointOffer answers past (payment quantity) (position quantity positive small) loss.key =
      some (jointReceipt quantity positive small) := by
  unfold Settlement.jointOffer
  rw [dif_pos ⟨rfl, rfl, (jointReceipt quantity positive small).positive⟩]
  rfl

private theorem one_material_position :
    itemPositions (seed := Original.seed) past (payment quantity) = [position quantity positive small] := by
  have width : (Boundary.Actual.items (endAt Original.seed past) (payment quantity)).length = 1 :=
    congrArg List.length (original_payment_items quantity positive small)
  obtain ⟨site, exactList⟩ := List.length_eq_one_iff.mp (List.length_finRange.trans width)
  change List.finRange (Boundary.Actual.items (endAt Original.seed past) (payment quantity)).length =
    [position quantity positive small]
  have same : site = position quantity positive small := by
    apply Fin.ext
    have atZero := site.isLt.trans_eq width
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ atZero)
  rw [exactList, same]

include positive small in
private theorem posted_portfolio :
    (posted (reached answers loss [none]) (payment quantity)).stack.balances = [(loss, Original.balance)] := by
  have absent : openings Original.seed Original.community past (payment quantity) = [] := by
    unfold openings
    rw [the_payer_signs_without_any_new_loss quantity positive small]
    rfl
  rw [posted_balances, accounting_portfolio, absent, List.map_nil, List.append_nil]

private theorem actual_demand :
    Settlement.demand (Settlement.jointOffer answers past (payment quantity)
      (position quantity positive small)) false (posted (reached answers loss [none]) (payment quantity)).stack.balances = 6 := by
  classical
  have later : jointLater loss (jointReceipt quantity positive small) :=
    Or.inl (List.prefix_append born [none])
  rw [posted_portfolio quantity positive small]
  change (if loss.key.2.2 = false then Settlement.rowDemand
      (Settlement.jointOffer answers past (payment quantity) (position quantity positive small))
      loss Original.balance else 0) + 0 = 6
  simp only [show loss.key.2.2 = false from rfl, if_true, add_zero, Settlement.rowDemand,
    joint_offer quantity positive small, if_pos later, Original.balance_six]

include positive small in
theorem the_real_original_residual_is_six_less_the_partial_payment :
    (balance answers loss (word quantity)).remaining = 6 - quantity := by
  let state := posted (reached answers loss [none]) (payment quantity)
  let site := position quantity positive small
  let plan := Settlement.atPosition answers past (payment quantity) site state
  have cap : Settlement.limitAt past (payment quantity) site false = quantity :=
    (Settlement.the_original_limit_is_the_selected_quantity answers past (payment quantity) site loss.key
      (jointReceipt quantity positive small) (joint_offer quantity positive small)).trans
      (the_actual_payer_credit_equals_the_requested_quantity quantity positive small site)
  have charge := plan.tight false
  change Settlement.limitAt past (payment quantity) site false - (plan.left.balance false).remaining =
    min (Settlement.limitAt past (payment quantity) site false)
      (Settlement.demand (Settlement.jointOffer answers past (payment quantity) site) false state.stack.balances) at charge
  rw [cap, actual_demand quantity positive small, min_eq_left small.le] at charge
  have old : Settlement.outstanding false state.stack.balances = 6 := by
    rw [posted_portfolio quantity positive small]
    change (if loss.key.2.2 = false then Original.balance.remaining else 0) + 0 = 6
    simp only [show loss.key.2.2 = false from rfl, if_true, add_zero, Original.balance_six]
  have paid := plan.conservation false
  change Settlement.outstanding false plan.after.balances +
    (Settlement.limitAt past (payment quantity) site false - (plan.left.balance false).remaining) =
      Settlement.outstanding false state.stack.balances at paid
  rw [cap, charge, old] at paid
  have actual : (reached answers loss (word quantity)).stack.balances = plan.after.balances := by
    change (writeAfter answers (originState loss) ([none] ++ [payment quantity])).stack.balances = _
    rw [writeAfter_snoc_balances, Settlement.writeTick_balances, one_material_position quantity positive small,
      Settlement.writePositions, Settlement.writePositions, Settlement.writePosition_balances]
    rfl
  have origins := plan.move.keeps_origins
  rw [posted_portfolio quantity positive small] at origins
  have count : plan.after.balances.length = 1 := by
    simpa using congrArg List.length origins
  obtain ⟨row, exactRows⟩ := List.length_eq_one_iff.mp count
  have listed := balance_is_in_the_reached_rows answers loss (word quantity)
  rw [actual, exactRows] at listed
  have exactRow := List.mem_singleton.mp listed
  rw [exactRows, ← exactRow] at paid
  change (if loss.key.2.2 = false then (balance answers loss (word quantity)).remaining else 0) + 0 + quantity = 6 at paid
  simp only [show loss.key.2.2 = false from rfl, if_true, add_zero] at paid
  linarith only [paid]

#print axioms the_real_original_residual_is_six_less_the_partial_payment

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Unbounded.Nonattainment
