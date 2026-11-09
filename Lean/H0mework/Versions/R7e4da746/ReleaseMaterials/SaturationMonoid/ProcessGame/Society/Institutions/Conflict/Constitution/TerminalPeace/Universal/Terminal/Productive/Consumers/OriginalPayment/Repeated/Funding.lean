import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Repeated.Origins
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment.Repeated.Funding.Ledger

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Quantities.Execution (endAt)
open Reparation.Actual
open ExposureGuard (no_material_is_admitted)
open private append_eligible from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Consumers.OriginalPayment

noncomputable section

/-- The first native head accounts for the last levy. Each production lot
then consumes its own original material write and accounting head. -/
def fundingPrefix : Nat → Original.Word
  | 0 => [none]
  | count + 1 => (fundingPrefix count ++ [produceInput]) ++ [none]

abbrev fundedPast (n count : Nat) : Original.Word := birth n ++ fundingPrefix count
abbrev fundedState (n count : Nat) := Occurrence.reached replies (indexedLoss n) (fundingPrefix count)
abbrev fundedCut (n count : Nat) := endAt Original.seed (fundedPast n count)

private theorem extends_funding (n count : Nat) : fundedPast n (count + 1) = fundedPast n count ++ productionHead := by
  simp only [fundedPast, fundingPrefix, List.append_assoc]
  rfl

/-- Any finite number of original material lots is actually produced and
booked on the same source, retaining each original restitution row. -/
theorem funding_is_actual_at_every_count (n count : Nat) :
    Occurrence.Eligible replies (indexedLoss n) (fundingPrefix count) ∧
    (fundedCut n count).raw = Snapshot 0 (113 + 18 * (count : ℚ)) ∧
    (Ready (fundedCut n count) ∧ ReviewAvailable (fundedCut n count)) ∧
    (fundedState n count).stack.balances = (fundedState n 0).stack.balances := by
  induction count with
  | zero =>
    have cut := actual_accounted_cut n
    have empty := native_head_is_empty n
    refine ⟨⟨⟨no_material_is_admitted _ _ _ _ empty,
      Boundary.Actual.no_material_write_has_no_damage _ _ _ empty⟩, trivial⟩, ?_, cut.2, rfl⟩
    change (endAt Original.seed (accounted n)).raw = _
    simpa only [Nat.cast_zero, mul_zero, add_zero] using cut.1
  | succ count earlier =>
    obtain ⟨eligible, stock, ⟨ready, review⟩, balances⟩ := earlier
    have effect := production_adds_eighteen_to_the_actual_original_inventory (fundedPast n count) ready review _ stock
    have checked := the_production_and_accounting_are_eligible (fundedPast n count) ready review (birth n)
    have word : fundingPrefix (count + 1) = fundingPrefix count ++ productionHead := by
      rw [fundingPrefix, List.append_assoc]
      rfl
    refine ⟨(congrArg (Occurrence.Eligible replies (indexedLoss n)) word).mpr (append_eligible eligible checked), ?_, ?_, ?_⟩
    · change (endAt Original.seed (fundedPast n (count + 1))).raw = _
      rw [extends_funding, effect.1, Nat.cast_succ]
      congr 1
      ring
    · change Ready (endAt Original.seed (fundedPast n (count + 1))) ∧
        ReviewAvailable (endAt Original.seed (fundedPast n (count + 1)))
      rw [extends_funding]
      exact effect.2
    · have noItems : Boundary.Actual.items
          (endAt Original.seed (birth n ++ (fundingPrefix count ++ [produceInput]))) none = [] := by
        simpa only [fundedPast, List.append_assoc] using production_accounting_has_no_item (fundedPast n count) ready review
      change (Occurrence.writeAfter replies (Occurrence.originState (indexedLoss n))
        ((fundingPrefix count ++ [produceInput]) ++ [none])).stack.balances = _
      rw [Occurrence.writeAfter_snoc_balances, a_native_accounting_input_keeps_the_entire_balance_table _ _ noItems,
        Occurrence.writeAfter_snoc_balances]
      exact (production_keeps_the_original_portfolio (fundedState n count) ready review).trans balances

theorem the_funded_cut_keeps_the_exact_total_due (n count : Nat) :
    let rows := (fundedState n count).stack.balances
    (∀ row ∈ rows, row.1.key = (indexedLoss n).key ∧ (Occurrence.history row.1).IsPrefix (fundedPast n count)) ∧
      Settlement.outstanding false rows = 6 * ((n : ℚ) + 1) := by
  dsimp only
  rw [(funding_is_actual_at_every_count n count).2.2.2]
  have original := the_original_portfolio_is_all_due n
  have retained : (accounted n).IsPrefix (fundedPast n count) := by
    induction count with
    | zero => exact List.prefix_rfl
    | succ count older =>
      rw [extends_funding]
      exact older.trans (List.prefix_append _ _)
  exact ⟨fun row listed => ⟨(original.1 row listed).1, (original.1 row listed).2.trans retained⟩, original.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.OriginalPayment.Repeated
