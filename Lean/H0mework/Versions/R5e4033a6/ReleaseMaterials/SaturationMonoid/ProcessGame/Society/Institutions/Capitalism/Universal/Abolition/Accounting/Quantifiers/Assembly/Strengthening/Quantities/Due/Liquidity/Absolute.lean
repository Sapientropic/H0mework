import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Holding
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile

variable {Address Row Item : Type*}
  [Fintype Row] [Fintype Item] [DecidableEq Address]

/-- Absolute opening stock required for the same admitted debits and credits.
The stock before each debit is measured relative to the original opening. -/
def openingReserveThrough (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (horizon : ℚ) (address : Address) : ℚ :=
  ({ view with opening := fun _ => 0 } : Profile Address Row Item).rollingReserveThrough
    (fun item key => before item key - view.opening key) horizon address

theorem openingReserveThrough_fits_iff (view : Profile Address Row Item)
    (before : Item → Address → ℚ) (horizon : ℚ) (address : Address) (opening : ℚ) :
    view.openingReserveThrough before horizon address ≤ opening ↔
      0 ≤ opening ∧
      (∀ time, view.start ≤ time → time ≤ horizon →
        view.grossDue time address + view.otherDebits time address ≤ opening + view.credited time address) ∧
      (∀ item, view.commit item ≤ horizon → view.pastDue (view.commit item) address +
        view.debit item address ≤ before item address - view.opening address + opening) := by
  let origin : Profile Address Row Item := { view with opening := fun _ => 0 }
  unfold openingReserveThrough
  change origin.rollingReserveThrough _ _ _ ≤ _ ↔ _
  rw [origin.rollingReserveThrough_fits_iff]
  have after (time : ℚ) :
      origin.gap time address ≤ opening ↔
        view.grossDue time address + view.otherDebits time address ≤ opening + view.credited time address := by
    rw [origin.same_due_receipt_is_not_charged_twice]
    change view.grossDue time address + view.otherDebits time address - 0 -
      view.credited time address ≤ opening ↔ _
    rw [sub_zero, sub_le_iff_le_add]
  simp only [after]
  rfl



theorem extra_reserve_is_the_positive_part_of_the_absolute_opening_gap
    (view : Profile Address Row Item) (before : Item → Address → ℚ)
    (horizon : ℚ) (address : Address) (opening : 0 ≤ view.opening address) :
    view.rollingReserveThrough before horizon address =
      max 0 (view.openingReserveThrough before horizon address - view.opening address) := by
  apply eq_of_forall_ge_iff
  intro extra
  rw [max_le_iff, sub_le_iff_le_add, view.openingReserveThrough_fits_iff, view.rollingReserveThrough_fits_iff]
  refine and_congr_right fun nonnegative => ?_
  have full : 0 ≤ extra + view.opening address := add_nonneg nonnegative opening
  simp only [full, true_and]
  constructor
  · rintro ⟨after, beforeDebit⟩
    refine ⟨fun time start within => ?_, fun item within => ?_⟩
    have bound := after time start within
    rw [view.same_due_receipt_is_not_charged_twice] at bound
    linarith only [bound]
    have bound := beforeDebit item within
    linarith only [bound]
  · rintro ⟨after, beforeDebit⟩
    refine ⟨fun time start within => ?_, fun item within => ?_⟩
    have bound := after time start within
    rw [view.same_due_receipt_is_not_charged_twice]
    linarith only [bound]
    have bound := beforeDebit item within
    linarith only [bound]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Profile
