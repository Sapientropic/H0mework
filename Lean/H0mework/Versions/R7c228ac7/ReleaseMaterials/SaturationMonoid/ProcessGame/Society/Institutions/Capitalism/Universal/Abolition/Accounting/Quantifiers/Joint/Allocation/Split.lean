import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Duty.State
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation

/-- The source quota receives priority; only the unassigned part is offered
again. No payment amount is independently reused by the second row. -/
def first (quota amount : ℚ) : ℚ := min quota (max 0 amount)
def rest (quota amount : ℚ) : ℚ := max 0 amount - first quota amount
def second (firstQuota secondQuota amount : ℚ) : ℚ := min secondQuota (rest firstQuota amount)

theorem first_nonnegative (quota amount : ℚ) (nonnegative : 0 ≤ quota) : 0 ≤ first quota amount :=
  le_min nonnegative (le_max_left _ _)

theorem rest_nonnegative (quota amount : ℚ) : 0 ≤ rest quota amount :=
  sub_nonneg.mpr (min_le_right _ _)

theorem second_nonnegative (firstQuota secondQuota amount : ℚ) (nonnegative : 0 ≤ secondQuota) :
    0 ≤ second firstQuota secondQuota amount := le_min nonnegative (rest_nonnegative _ _)

theorem a_single_original_credit_is_never_spent_twice (firstQuota secondQuota amount : ℚ) :
    first firstQuota amount + second firstQuota secondQuota amount ≤ max 0 amount := by
  have after := min_le_right secondQuota (rest firstQuota amount)
  unfold second at *
  unfold rest at *
  linarith

theorem first_does_not_exceed_its_original_quota (quota amount : ℚ) : first quota amount ≤ quota := min_le_left _ _

theorem second_does_not_exceed_its_original_quota (firstQuota secondQuota amount : ℚ) :
    second firstQuota secondQuota amount ≤ secondQuota := min_le_left _ _

theorem zero_actual_credit_cannot_discharge_either_row (firstQuota secondQuota : ℚ)
    (firstNonnegative : 0 ≤ firstQuota) (secondNonnegative : 0 ≤ secondQuota) :
    first firstQuota 0 = 0 ∧ second firstQuota secondQuota 0 = 0 := by
  simp [first,second,rest,min_eq_right firstNonnegative,min_eq_right secondNonnegative]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation
