import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve.Original
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve

open scoped BigOperators

variable {Row Address : Type*} {n : ℕ}

def assignedAt (paid : Row → Fin n → ℚ) (row : Row) (ordinal : ℕ) : ℚ :=
  if inside : ordinal < n then paid row ⟨ordinal, inside⟩ else 0

/-- Only ordinals strictly before the cut are paid. Equal commit clocks
never merge different material items or re-open a paid row. -/
def paidBefore (paid : Row → Fin n → ℚ) (cut : ℕ) (row : Row) : ℚ :=
  ∑ i : Fin n, if i.val < cut then paid row i else 0

theorem paidBefore_next (paid : Row → Fin n → ℚ) (i : Fin n) (row : Row) :
    paidBefore paid (i.val + 1) row = paidBefore paid i.val row + paid row i := by
  unfold paidBefore
  calc
    _ = ∑ j : Fin n, ((if j.val < i.val then paid row j else 0) +
        (if j = i then paid row j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases same : j = i
      · subst j
        simp
      · have distinct : j.val ≠ i.val := fun h => same (Fin.ext h)
        have before : j.val < i.val + 1 ↔ j.val < i.val := by omega
        simp [same, before]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem assignedAt_original (paid : Row → Fin n → ℚ) (i : Fin n) (row : Row) :
    assignedAt paid row i.val = paid row i :=
  dif_pos i.isLt

theorem held_eq_roster_sum [DecidableEq Row] [DecidableEq Address] (rows : List Row) (once : rows.Nodup)
    (address : Row → Address) (amount : Row → ℚ) (key : Address) :
    held rows address amount key = ∑ row ∈ rows.toFinset, atAddress address amount key row := by
  rw [List.sum_toFinset _ once]
  rfl

open Quantities.Due.Liquidity

variable [Fintype Row] [DecidableEq Address]

variable {view : Profile Address Row (Fin n)}

theorem original_prefix_payment_le_required (accounted : view.Conservative) (cut : ℕ) (row : Row) :
    paidBefore view.paid cut row ≤ view.required row := by
  apply le_trans _ (accounted.perRow row)
  apply Finset.sum_le_sum
  intro i _
  split
  · exact le_rfl
  · exact accounted.nonnegative row i

theorem original_paid_row_cannot_be_paid_again (accounted : view.Conservative)
    (cut : ℕ) (i : Fin n) (later : cut ≤ i.val) (row : Row)
    (closed : paidBefore view.paid cut row = view.required row) :
    view.paid row i = 0 := by
  have next := original_prefix_payment_le_required accounted (i.val + 1) row
  rw [paidBefore_next] at next
  have monotone : paidBefore view.paid cut row ≤ paidBefore view.paid i.val row := by
    apply Finset.sum_le_sum
    intro j _
    split
    · rename_i previous
      rw [if_pos (previous.trans_le later)]
    · split
      · exact accounted.nonnegative row j
      · exact le_rfl
  linarith only [next, monotone, closed, accounted.nonnegative row i]

theorem debit_pays_the_old_and_new_rows_only_once [DecidableEq Row] (accounted : view.Conservative)
    (rows : List Row) (once : rows.Nodup) (i : Fin n) (key : Address) :
    held rows view.address (fun row => assignedAt view.paid row i.val) key ≤ view.debit i key := by
  rw [held_eq_roster_sum rows once]
  simp only [assignedAt_original, atAddress]
  apply le_trans _ (accounted.perDebit i key)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro row _ _
  split
  · exact accounted.nonnegative row i
  · exact le_rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Reserve
