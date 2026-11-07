import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant

open Source.Program PublicFunction.Repayment
open Redemption (essentials unit rate creditorStock debtorStock lower)

section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument)
  (position : Position Party Instrument)

def issue (quantity : ℚ) : Request Party Good Port Technology Instrument :=
  ⟨position.debtor, [], law.issuerPort position.instrument, [],
    .issue position.instrument position.debtor position.creditor quantity⟩

def word (quantity : ℚ) : RawEvent Party Good Port Technology Instrument :=
  [issue law position quantity, Redemption.request law position quantity]

def stockCeiling : ℚ :=
  (debtorStock law current position - essentials law origin position.debtor (unit law position)) /
    rate law position

def Qualified (quantity : ℚ) : Prop :=
  law.Valid current (issue law position quantity) ∧
    Redemption.Safe law origin (law.step current (issue law position quantity)) position quantity

theorem issue_keeps_all_real_stock (quantity : ℚ) :
    (law.step current (issue law position quantity)).stock = current.stock :=
  law.issuance_creates_no_material current (issue law position quantity)
    position.instrument position.debtor position.creditor quantity rfl

theorem issue_credits_exactly_its_original_claim_address (quantity : ℚ)
    (accepted : law.Valid current (issue law position quantity)) :
    balance position (law.step current (issue law position quantity)) = balance position current + quantity := by
  unfold balance
  rw [law.step_financial_balance, law.accepted_delta _ _ accepted]
  simp [RawLaw.claimDelta, issue]

/-- Issuing a grant changes the claim budget, while the full redemption
still consumes the issuer's original material capacity. -/
theorem every_grant_is_exactly_checked_at_its_source_floor_and_stock_ceiling (quantity : ℚ) :
    Qualified law origin current position quantity ↔
      law.Valid current (issue law position quantity) ∧
      position.debtor ≠ position.creditor ∧ 0 < rate law position ∧
      0 ≤ balance position current ∧
      lower law origin current position ≤ quantity ∧ quantity ≤ stockCeiling law origin current position ∧
      Redemption.Authorized law (law.step current (issue law position quantity)) position quantity := by
  have sameStock := issue_keeps_all_real_stock law current position quantity
  have lowerEq : lower law origin (law.step current (issue law position quantity)) position =
      lower law origin current position := by
    simp only [Redemption.lower, creditorStock, sameStock]
  have capacityEq : Redemption.upper law origin (law.step current (issue law position quantity)) position =
      min (balance position (law.step current (issue law position quantity))) (stockCeiling law origin current position) := by
    simp only [Redemption.upper, stockCeiling, debtorStock, sameStock]
  unfold Qualified
  rw [Redemption.safe_iff_original_authority_and_tight_material_interval]
  constructor
  · rintro ⟨issued, distinct, ratePositive, ⟨enough, within⟩, gate⟩
    rw [lowerEq] at enough
    rw [capacityEq, issue_credits_exactly_its_original_claim_address law current position quantity issued, le_min_iff] at within
    exact ⟨issued, distinct, ratePositive, by linarith [within.1], enough, within.2, gate⟩
  · rintro ⟨issued, distinct, ratePositive, old, enough, stock, gate⟩
    refine ⟨issued, distinct, ratePositive, ⟨?_, ?_⟩, gate⟩
    · simpa only [lowerEq] using enough
    · rw [capacityEq, issue_credits_exactly_its_original_claim_address law current position quantity issued, le_min_iff]
      exact ⟨le_add_of_nonneg_left old, stock⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant
