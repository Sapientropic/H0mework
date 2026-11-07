import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Raw.Flow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

def claimTotal (current : RawCurrent Bool Bool Nat Unit) : ℚ :=
  current.claims () false false + current.claims () false true + current.claims () true false + current.claims () true true

theorem issue_adds_its_original_quantity (current : RawCurrent Bool Bool Nat Unit)
    (instruction : Request Bool Bool Unit Nat Unit) (issuer holder : Bool) (quantity : ℚ)
    (operation : instruction.operation = .issue () issuer holder quantity) :
    claimTotal (law.paidStep current instruction) = claimTotal current + quantity := by
  cases issuer <;> cases holder <;> simp [claimTotal,RawLaw.paidStep,RawLaw.nextClaims,operation] <;> ring

theorem an_assignment_preserves_the_complete_original_debt_total (current : RawCurrent Bool Bool Nat Unit)
    (instruction : Request Bool Bool Unit Nat Unit) (issuer sender holder : Bool) (quantity : ℚ)
    (operation : instruction.operation = .assign () issuer sender holder quantity) :
    claimTotal (law.paidStep current instruction) = claimTotal current := by
  cases issuer <;> cases sender <;> cases holder <;> simp [claimTotal,RawLaw.paidStep,RawLaw.nextClaims,operation] <;> ring

theorem cash_zero_prevents_any_reduction_of_complete_debt
    (current : RawCurrent Bool Bool Nat Unit) (instruction : Request Bool Bool Unit Nat Unit)
    (nonnegative : StockNonnegative current) (empty : CashZero current) :
    claimTotal current ≤ claimTotal (law.step current instruction) := by
  by_cases accepted : law.Valid current instruction
  · rw [RawLaw.step,if_pos accepted]
    cases operation : instruction.operation with
    | issue instrument issuer holder quantity =>
        cases instrument
        rw [issue_adds_its_original_quantity current instruction issuer holder quantity operation]
        have guard := accepted.2.2.1
        simp only [RawLaw.ClaimGuard,operation] at guard
        exact le_add_of_nonneg_right guard
    | assign instrument issuer sender holder quantity =>
        cases instrument
        rw [an_assignment_preserves_the_complete_original_debt_total current instruction issuer sender holder quantity operation]
    | settle instrument debtor holder quantity =>
        cases instrument
        have zero := no_cash_cannot_pay_positive_original_debt current instruction nonnegative empty accepted debtor holder quantity operation
        simp [claimTotal,RawLaw.paidStep,RawLaw.nextClaims,operation,zero]
    | produce operator | transfer sender receiver goods | use bearer goods purpose | revise operator technology | present =>
        simp [claimTotal,RawLaw.paidStep,RawLaw.nextClaims,operation]
  · rw [law.rejected_preserves_current current instruction accepted]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment
