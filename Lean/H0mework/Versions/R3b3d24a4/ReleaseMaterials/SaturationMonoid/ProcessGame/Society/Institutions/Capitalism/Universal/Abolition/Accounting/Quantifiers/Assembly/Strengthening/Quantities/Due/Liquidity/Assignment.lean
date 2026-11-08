import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Holding

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile

open scoped BigOperators

variable {Address Row Item : Type*}
variable [Fintype Row] [Fintype Item] [DecidableEq Address]

/-- The source's assignment certificate splits each original debit at most
once per address and never pays a row beyond its original amount. -/
structure Conservative (view : Profile Address Row Item) : Prop where
  nonnegative : ∀ row item, 0 ≤ view.paid row item
  perRow : ∀ row, (∑ item, view.paid row item) ≤ view.required row
  perDebit : ∀ item address, (∑ row, if view.address row = address then view.paid row item else 0) ≤
    view.debit item address

theorem Conservative.paidThrough_le {view : Profile Address Row Item}
    (accounted : view.Conservative) (time : ℚ) (row : Row) :
    view.paidThrough time row ≤ view.required row := by
  apply le_trans _ (accounted.perRow row)
  apply Finset.sum_le_sum
  intro item _
  split
  · exact le_rfl
  · exact accounted.nonnegative row item

theorem Conservative.outstanding_nonnegative {view : Profile Address Row Item}
    (accounted : view.Conservative) (time : ℚ) (address : Address) :
    0 ≤ view.outstandingDue time address := by
  apply Finset.sum_nonneg
  intro row _
  split
  · exact sub_nonneg.mpr (accounted.paidThrough_le time row)
  · exact le_rfl

theorem Conservative.otherDebits_nonnegative {view : Profile Address Row Item}
    (accounted : view.Conservative) (time : ℚ) (address : Address) :
    0 ≤ view.otherDebits time address := by
  unfold otherDebits
  apply Finset.sum_nonneg
  intro item _
  split
  · apply sub_nonneg.mpr
    apply le_trans _ (accounted.perDebit item address)
    apply Finset.sum_le_sum
    intro row _
    by_cases owned : view.address row = address
    · rw [if_pos owned]
      split
      · exact le_rfl
      · exact accounted.nonnegative row item
    · simp [owned]
  · exact le_rfl

theorem outstanding_shortage_names_an_original_row (view : Profile Address Row Item)
    (time : ℚ) (address : Address) (short : 0 < view.outstandingDue time address) :
    ∃ row, view.address row = address ∧ view.deadline row ≤ time ∧
      view.paidThrough time row < view.required row := by
  classical
  by_contra none
  have zero : view.outstandingDue time address ≤ 0 := by
    unfold outstandingDue
    apply Finset.sum_nonpos
    intro row _
    split
    · rename_i due
      exact sub_nonpos.mpr (le_of_not_gt fun deficit => none ⟨row, due.1, due.2, deficit⟩)
    · exact le_rfl
  exact (not_le_of_gt short) zero

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile
