import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Funding
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Payment
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Renewal

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open Reparation.Actual (ReceiptAnswers)
open ExposureGuard.Exit (SignersChose)
open Runtime.Viability (Move)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community)

/-- The paid opening period and its local original production laws. -/
structure ProductionPilot where
  move : FundingMove loss
  quantum : ℚ
  accumulation : move.AccumulationLaw quantum
  registration : Move.RegistrationOnReserves seed.native.input (originalRaw loss)
  reserve_nonnegative : ∀ person good, 0 ≤ (originalRaw loss).stock person good

variable (pilot : ProductionPilot loss)

abbrev gainAt (cell : MaterialCell Party Good) : ℚ :=
  Balance.gain seed.native.input.law (originalRaw loss) pilot.move.word cell.1 cell.2

/-- Each still-owed physical account can earn its own reparation stock
while the opening productive reserve is protected. -/
def CoversEveryOriginalDebt : Prop :=
  ∀ cell, 0 < cellDue (Occurrence.originState loss).stack.balances cell → 0 < gainAt loss pilot cell

def fundingBound (grows : CoversEveryOriginalDebt loss pilot) :
    {n : Nat // Funds (Occurrence.originState loss).stack.balances (fun _ => 0) (gainAt loss pilot) n ∧
      ∀ m, Funds (Occurrence.originState loss).stack.balances (fun _ => 0) (gainAt loss pilot) m → n ≤ m} := by
  have nonnegative (cell : MaterialCell Party Good) : 0 ≤ gainAt loss pilot cell :=
    (Balance.checked_productive_period _ _ _ pilot.accumulation.accumulating).2 _ _
  have feasible := fundingCycles_le_iff_funds (Occurrence.originState loss).stack.balances (fun _ => 0)
    (gainAt loss pilot) (fun _ => le_rfl) nonnegative grows
  exact ⟨_, (feasible _).mp le_rfl, fun n paid => (feasible n).mpr paid⟩

variable (answers : ReceiptAnswers seed)

abbrev FundingCovers (n : Nat) :=
  CoversPortfolio loss answers (originalRaw loss).stock (fundingWord loss pilot.move n)

structure NativeFundingApproved (n : Nat) : Prop where
  review : ReviewAvailable (endAt seed (Occurrence.history loss))
  guards : ∀ k < n, FundingChecks (fundingCut loss pilot.move k) (originalRaw loss) (originalBearers loss) pilot.move.word ∧
    SignersChose answers (Occurrence.history loss ++ fundingWord loss pilot.move k) [some (.execute pilot.move.word)]

/-- Each next period is authorized only while an actual earlier prefix
has yet to meet the whole protected reserve. -/
structure FundingRelease (bound : Nat) : Prop where
  review : ReviewAvailable (endAt seed (Occurrence.history loss))
  next : ∀ k < bound, NativeFundingApproved loss pilot answers k →
    (∀ earlier ≤ k, ¬ FundingCovers loss pilot answers earlier) →
    FundingChecks (fundingCut loss pilot.move k) (originalRaw loss) (originalBearers loss) pilot.move.word ∧
      SignersChose answers (Occurrence.history loss ++ fundingWord loss pilot.move k) [some (.execute pilot.move.word)]

abbrev actual_funding {n : Nat} (approved : NativeFundingApproved loss pilot answers n) :=
  funding_is_actual loss pilot.move pilot.accumulation answers n approved.review
    (fun k early => (approved.guards k early).1) (fun k early => (approved.guards k early).2)

private theorem an_approved_full_budget_funds_the_actual_portfolio {n : Nat}
    (approved : NativeFundingApproved loss pilot answers n)
    (budget : Funds (Occurrence.originState loss).stack.balances (fun _ => 0) (gainAt loss pilot) n) :
    FundingCovers loss pilot answers n := by
  have actual := actual_funding loss pilot answers approved
  have changed := a_safe_suffix_can_only_decrease_the_original_balances answers (Occurrence.history loss)
    (Occurrence.originState loss) (fundingWord loss pilot.move n) actual.1
  intro person good
  have caps := (changed.cellDue_le (person, good)).trans (budget (person, good))
  rw [zero_add] at caps
  change _ ≤ (fundingCut loss pilot.move n).raw.stock person good
  rw [actual.2.2.2.1 person good]
  exact add_le_add_right (show cellDue (prefixRows loss answers (fundingWord loss pilot.move n)) (person, good) ≤
    (n : ℚ) * Balance.gain seed.native.input.law (originalRaw loss) pilot.move.word person good from caps) _

theorem a_finite_original_funding_prefix_covers_all_cells
    (grows : CoversEveryOriginalDebt loss pilot)
    (release : FundingRelease loss pilot answers (fundingBound loss pilot grows).val) :
    ∃ n ≤ (fundingBound loss pilot grows).val,
      NativeFundingApproved loss pilot answers n ∧ FundingCovers loss pilot answers n := by
  let bound := fundingBound loss pilot grows
  by_contra missing
  have approved (n : Nat) (within : n ≤ bound.val) : NativeFundingApproved loss pilot answers n := by
    induction n with
    | zero => exact ⟨release.review, fun _ impossible => (Nat.not_lt_zero _ impossible).elim⟩
    | succ k earlier =>
      have previous := earlier (Nat.le_of_succ_le within)
      have noPayment (j : Nat) (noLater : j ≤ k) : ¬ FundingCovers loss pilot answers j :=
        fun possible => missing ⟨j, noLater.trans (Nat.le_of_succ_le within),
          ⟨previous.review, fun i before => previous.guards i (before.trans_le noLater)⟩, possible⟩
      have released := release.next k (Nat.lt_of_succ_le within) previous noPayment
      refine ⟨previous.review, fun i before => ?_⟩
      by_cases early : i < k
      · exact previous.guards i early
      · have exactIndex : i = k := by omega
        exact exactIndex.symm ▸ released
  have actual := approved bound.val le_rfl
  exact missing ⟨bound.val, le_rfl, actual,
    an_approved_full_budget_funds_the_actual_portfolio loss pilot answers actual bound.property.1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
