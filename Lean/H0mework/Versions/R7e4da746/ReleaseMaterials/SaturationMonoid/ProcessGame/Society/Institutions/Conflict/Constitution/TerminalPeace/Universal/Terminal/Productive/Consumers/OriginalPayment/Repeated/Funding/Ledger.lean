import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Repeated.Funding.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Balance

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Quantities.Execution (endAt)
open Reparation.Actual
open Reparation.Actual.Allocation (Position itemPositions originalItem)
open private balance_ext from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Balance

noncomputable section

private theorem allocation_without_any_offer_keeps_balances
    (offer : Settlement.JointOffer Original.seed) (limit : Bool → ℚ)
    (backed : ∀ key (receipt : JointReceipt Original.seed key), offer key = some receipt → limit key.2.2 ≤ receipt.quantity)
    {N J : WorldRelationNetwork} (before : Stack Original.seed Original.community N J)
    (available : Settlement.Available limit) (absent : ∀ key, offer key = none) :
    (Settlement.allocate offer limit backed before available).after.balances = before.balances := by
  induction before with
  | base => rfl
  | add prior origin before view earlier =>
    let priorAllocation := Settlement.allocate offer limit backed prior available
    let room := priorAllocation.left.balance origin.key.2.2
    let current := Settlement.allocateRow offer origin before room.remaining room.nonnegative
      (fun receipt selected => (priorAllocation.left.within origin.key.2.2).trans (backed origin.key receipt selected))
    change priorAllocation.after.balances ++ [(origin, current.after)] = prior.balances ++ [(origin, before)]
    have due : Settlement.rowDemand offer origin before = 0 := by simp [Settlement.rowDemand, absent]
    have noCharge : current.amount = 0 := by
      rw [current.exactAmount, due, min_eq_right room.nonnegative]
    have same : current.after = before := balance_ext (by rw [current.afterExact, noCharge, sub_zero])
    rw [earlier, same]

private theorem a_production_item_is_no_receipt (past : Original.Word) (ready : Ready (endAt Original.seed past))
    (review : ReviewAvailable (endAt Original.seed past)) (site : Position Original.seed past produceInput)
    (key : Reparation.Key Bool Bool) : Settlement.jointOffer replies past produceInput site key = none := by
  unfold Settlement.jointOffer
  apply dif_neg
  intro offered
  obtain ⟨_, _, _, _, transfer, _⟩ := positive_payer_credit_has_the_original_payer_and_delivery _ _ _ offered.2.2
  rw [the_produced_item_at past ready review site] at transfer
  cases transfer

/-- Producing new collateral does not prepay a restitution row. -/
theorem production_keeps_the_original_portfolio {past : Original.Word} (state : State Original.seed Original.community past)
    (ready : Ready (endAt Original.seed past)) (review : ReviewAvailable (endAt Original.seed past)) :
    (Settlement.writeTick replies state produceInput).stack.balances = state.stack.balances := by
  have width := congrArg List.length (the_production_item_is_actual past ready review)
  have one : (itemPositions (seed := Original.seed) past produceInput).length = 1 :=
    List.length_finRange.trans width
  obtain ⟨site, exactPositions⟩ := List.length_eq_one_iff.mp one
  rw [Settlement.writeTick_balances, exactPositions, Settlement.writePositions, Settlement.writePositions,
    Settlement.writePosition_balances]
  let postedState := posted state produceInput
  have same : postedState.stack.balances = state.stack.balances := by
    unfold postedState
    rw [posted_balances]
    have noOpening : openings Original.seed Original.community past produceInput = [] := by
      unfold openings
      rw [the_material_production_has_no_new_damage past ready review]
      rfl
    rw [noOpening, List.map_nil, List.append_nil]
  change (Settlement.atPosition replies past produceInput site postedState).after.balances = _
  refine (allocation_without_any_offer_keeps_balances _ _ _ postedState.stack _
    (a_production_item_is_no_receipt past ready review site)).trans same

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated
