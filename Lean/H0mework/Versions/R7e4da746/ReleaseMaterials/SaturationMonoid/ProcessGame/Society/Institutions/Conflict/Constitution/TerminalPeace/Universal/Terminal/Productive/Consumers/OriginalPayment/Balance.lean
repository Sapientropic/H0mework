import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Quantities.Execution (endAt)
open Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions)
open Occurrence.Unbounded.Nonattainment (loss born payment)

noncomputable section

theorem a_native_accounting_input_keeps_the_entire_balance_table
    {past : Original.Word} (state : State Original.seed Original.community past) (answers : ReceiptAnswers Original.seed)
    (absent : Boundary.Actual.items (endAt Original.seed past) none = []) :
    (Settlement.writeTick answers state none).stack.balances = state.stack.balances := by
  have empty : itemPositions (seed := Original.seed) past none = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp only [itemPositions, List.length_finRange, absent, List.length_nil]
  have noDamage : openings Original.seed Original.community past none = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ absent]
    rfl
  rw [Settlement.writeTick_balances, empty, Settlement.writePositions, posted_balances, noDamage, List.map_nil,
    List.append_nil]

variable {base : ℚ} (past : Original.Word) (paid quantity : ℚ)
  (stock : (endAt Original.seed past).raw = Snapshot paid base)
  (ready : Ready (endAt Original.seed past)) (review : ReviewAvailable (endAt Original.seed past))
  (positive : 0 < quantity) (funded : quantity ≤ base - paid)

include stock ready review positive funded

theorem the_two_actual_replies_issue_exactly_the_delivered_receipt
    (site : Position Original.seed past (payment quantity)) :
    ∃ receipt : JointReceipt Original.seed loss.key,
      Settlement.jointOffer replies past (payment quantity) site loss.key = some receipt ∧
      receipt.quantity = quantity := by
  have exactFlow := the_actual_delivery past paid quantity stock ready review positive funded site
  have payer := the_actual_reply past paid quantity stock ready review positive funded site loss.key.2.1
  have victim := the_actual_reply past paid quantity stock ready review positive funded site loss.key.1
  have delivered := exactFlow.symm ▸ positive
  refine ⟨⟨past, payment quantity, site, replies, payer, victim, delivered⟩, ?_, exactFlow⟩
  unfold Settlement.jointOffer
  rw [dif_pos ⟨payer, victim, delivered⟩]

theorem one_payment_position :
    ∃ site : Position Original.seed past (payment quantity),
      itemPositions (seed := Original.seed) past (payment quantity) = [site] := by
  have width := congrArg List.length (actual_items past paid quantity stock ready review positive funded)
  apply List.length_eq_one_iff.mp
  exact List.length_finRange.trans width

omit stock ready review positive funded in
private theorem sole_outstanding (old : Balance) :
    Settlement.outstanding false [(loss, old)] = old.remaining := by
  simp only [Settlement.outstanding, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    show loss.key.2.2 = false from rfl, if_true]

omit stock ready review positive funded in
private theorem balance_ext {left right : Balance} (same : left.remaining = right.remaining) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- The actual native installment spends its own freshly signed quantity
once, carrying the same original row even when the residual reaches zero. -/
theorem the_installment_pays_the_original_row
    (state : State Original.seed Original.community past) (old : Balance)
    (portfolio : state.stack.balances = [(loss, old)]) (later : born.IsPrefix past)
    (within : quantity ≤ old.remaining) :
    (Settlement.writeTick replies state (payment quantity)).stack.balances = [(loss, old.subtract quantity within)] := by
  classical
  obtain ⟨site, positions⟩ := one_payment_position past paid quantity stock ready review positive funded
  obtain ⟨receipt, issued, exactFlow⟩ :=
    the_two_actual_replies_issue_exactly_the_delivered_receipt past paid quantity stock ready review positive funded site
  have ordered : jointLater loss receipt := by
    obtain ⟨_, _, _, rfl⟩ := Settlement.the_joint_offer_is_issued_at_the_exact_position _ _ _ _ _ _ issued
    exact Or.inl later
  let postedState := posted state (payment quantity)
  have filed : postedState.stack.balances = [(loss, old)] := by
    unfold postedState
    rw [posted_balances, portfolio]
    have absent : openings Original.seed Original.community past (payment quantity) = [] := by
      unfold openings
      rw [the_return_has_no_new_damage past paid quantity stock ready review positive funded]
      rfl
    rw [absent, List.map_nil, List.append_nil]
  let plan := Settlement.atPosition replies past (payment quantity) site postedState
  have demand : Settlement.demand (Settlement.jointOffer replies past (payment quantity) site) false
      postedState.stack.balances = old.remaining := by
    rw [filed]
    simp only [Settlement.demand, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      show loss.key.2.2 = false from rfl, if_true, Settlement.rowDemand, issued, if_pos ordered]
  have cap : Settlement.limitAt past (payment quantity) site false = quantity :=
    (Settlement.the_original_limit_is_the_selected_quantity replies past (payment quantity) site loss.key
      receipt issued).trans exactFlow
  have charge := plan.tight false
  change Settlement.limitAt past (payment quantity) site false - (plan.left.balance false).remaining =
    min (Settlement.limitAt past (payment quantity) site false)
      (Settlement.demand (Settlement.jointOffer replies past (payment quantity) site) false postedState.stack.balances)
    at charge
  rw [cap, demand, min_eq_left within] at charge
  have conservation := plan.conservation false
  change Settlement.outstanding false plan.after.balances +
    (Settlement.limitAt past (payment quantity) site false - (plan.left.balance false).remaining) =
      Settlement.outstanding false postedState.stack.balances at conservation
  rw [cap, charge, filed, sole_outstanding] at conservation
  have origins := plan.move.keeps_origins
  rw [filed] at origins
  have one : plan.after.balances.length = 1 := by simpa using congrArg List.length origins
  obtain ⟨⟨origin, balance⟩, exactRows⟩ := List.length_eq_one_iff.mp one
  rw [exactRows] at origins
  have same : origin = loss := List.singleton_inj.mp origins
  subst origin
  rw [exactRows, sole_outstanding] at conservation
  have after : balance = old.subtract quantity within := by
    apply balance_ext
    change balance.remaining = old.remaining - quantity
    linarith only [conservation]
  rw [Settlement.writeTick_balances, positions, Settlement.writePositions, Settlement.writePositions,
    Settlement.writePosition_balances]
  change plan.after.balances = _
  rw [exactRows, after]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment
