import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Kernel

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Kernel

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]
  (cohort : List Party) (positive : List (Party × Good))
  (scope : List (Entitlement.Duty.Key (Party := Party) (Good := Good)))
  (readings : Readings Party Good Port Technology Instrument) (old : Party × Good → ℚ) (p g : Bool)

theorem gross_is_at_most_the_original_unpaid_cell (work : Working Party Good)
    (item : ExecutionItem Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    gross cohort positive scope readings old p g work item key ≤ work.gross key := by
  unfold gross
  split
  · split <;> try exact work.gross_nonnegative key
    split
    · exact min_le_left _ _
    · exact work.gross_nonnegative key
  · exact work.gross_nonnegative key

def grossCharged (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    Working Party Good → List (ExecutionItem Party Good Port Technology Instrument) → ℚ
  | _, [] => 0
  | work, item :: tail => gross cohort positive scope readings old p g work item key +
      grossCharged key (after cohort positive scope readings old p g work item) tail

theorem every_original_cell_has_exact_material_conservation
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good))
    (work : Working Party Good) (items : List (ExecutionItem Party Good Port Technology Instrument)) :
    (items.foldl (after cohort positive scope readings old p g) work).gross key +
      grossCharged cohort positive scope readings old p g key work items = work.gross key := by
  induction items generalizing work with
  | nil => exact add_zero _
  | cons item tail inherited =>
      have bound := gross_is_at_most_the_original_unpaid_cell cohort positive scope readings old p g work item key
      have later := inherited (after cohort positive scope readings old p g work item)
      simp only [List.foldl_cons,grossCharged]
      rw [← add_assoc,add_right_comm _ (gross _ _ _ _ _ _ _ _ _ _),later]
      change max 0 (work.gross key - gross cohort positive scope readings old p g work item key) +
        gross cohort positive scope readings old p g work item key = _
      rw [max_eq_right (sub_nonneg.mpr bound)]
      exact sub_add_cancel _ _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Kernel
