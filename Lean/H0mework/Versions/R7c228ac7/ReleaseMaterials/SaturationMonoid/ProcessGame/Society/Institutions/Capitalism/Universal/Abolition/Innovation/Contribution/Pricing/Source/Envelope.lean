import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic.Interval

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source

def envelope : List (ℚ × ℚ) → Option (ℚ × ℚ)
  | [] => none
  | first :: rest => match envelope rest with
    | none => some first
    | some later => some (max first.1 later.1, min first.2 later.2)

theorem envelope_none_iff (rows : List (ℚ × ℚ)) : envelope rows = none ↔ rows = [] := by
  cases rows with
  | nil => simp [envelope]
  | cons first rest => simp only [envelope]; split <;> simp

theorem envelope_is_exact (rows : List (ℚ × ℚ)) (bounds : ℚ × ℚ)
    (computed : envelope rows = some bounds) (transfer : ℚ) :
    (bounds.1 ≤ transfer ∧ transfer ≤ bounds.2) ↔
      ∀ row ∈ rows, row.1 ≤ transfer ∧ transfer ≤ row.2 := by
  induction rows generalizing bounds with
  | nil => simp [envelope] at computed
  | cons first rest ih =>
      cases later : envelope rest with
      | none =>
          have empty := (envelope_none_iff rest).mp later
          subst rest
          simp only [envelope] at computed
          cases Option.some.inj computed
          simp
      | some tail =>
          simp only [envelope, later] at computed
          have same : (max first.1 tail.1, min first.2 tail.2) = bounds := by
            exact Option.some.inj computed
          subst bounds
          rw [show (max first.1 tail.1 ≤ transfer ∧ transfer ≤ min first.2 tail.2) ↔
            (first.1 ≤ transfer ∧ transfer ≤ first.2) ∧
              (tail.1 ≤ transfer ∧ transfer ≤ tail.2) by
                simp only [max_le_iff, le_min_iff]; tauto]
          rw [ih tail later]
          simp

structure Quote (rows : List (ℚ × ℚ)) where
  private mk ::
  bounds : ℚ × ℚ
  computed : envelope rows = some bounds
  compatible : bounds.1 ≤ bounds.2

def Quote.transfer {rows : List (ℚ × ℚ)} (quote : Quote rows) : ℚ :=
  Arithmetic.canonicalTransfer quote.bounds.1 quote.bounds.2

inductive QuoteIssue (rows : List (ℚ × ℚ)) where
  | empty (noBranches : rows = [])
  | incompatible (bounds : ℚ × ℚ) (computed : envelope rows = some bounds)
      (crossed : ¬ bounds.1 ≤ bounds.2)

inductive QuoteOutcome (rows : List (ℚ × ℚ)) where
  | priced (quote : Quote rows)
  | obstructed (issue : QuoteIssue rows)

def quote (rows : List (ℚ × ℚ)) : QuoteOutcome rows :=
  match computed : envelope rows with
  | none => .obstructed (.empty ((envelope_none_iff rows).mp computed))
  | some bounds =>
      if compatible : bounds.1 ≤ bounds.2 then .priced ⟨bounds, computed, compatible⟩
      else .obstructed (.incompatible bounds computed compatible)

theorem Quote.all_branches {rows : List (ℚ × ℚ)} (plan : Quote rows) :
    ∀ row ∈ rows, row.1 ≤ plan.transfer ∧ plan.transfer ≤ row.2 :=
  (envelope_is_exact rows plan.bounds plan.computed plan.transfer).mp
    (Arithmetic.canonical_transfer_is_in_the_interval _ _ plan.compatible)

theorem Quote.least_actual_payment {rows : List (ℚ × ℚ)} (plan : Quote rows) (other : ℚ)
    (safe : ∀ row ∈ rows, row.1 ≤ other ∧ other ≤ row.2) : |plan.transfer| ≤ |other| :=
  Arithmetic.canonical_transfer_has_minimal_absolute_payment _ _ _
    ((envelope_is_exact rows plan.bounds plan.computed other).mpr safe)

theorem Quote.unique_least_payment {rows : List (ℚ × ℚ)} (plan : Quote rows) (other : ℚ)
    (safe : ∀ row ∈ rows, row.1 ≤ other ∧ other ≤ row.2) (different : other ≠ plan.transfer) :
    |plan.transfer| < |other| :=
  Arithmetic.any_different_safe_transfer_has_strictly_larger_absolute_payment _ _ _
    ((envelope_is_exact rows plan.bounds plan.computed other).mpr safe) different

theorem QuoteIssue.no_safe_contract {rows : List (ℚ × ℚ)} (issue : QuoteIssue rows)
    (nonempty : rows ≠ []) : ¬ ∃ transfer : ℚ, ∀ row ∈ rows, row.1 ≤ transfer ∧ transfer ≤ row.2 := by
  rintro ⟨transfer, safe⟩
  cases issue with
  | empty empty => exact nonempty empty
  | incompatible bounds computed crossed =>
      have within := (envelope_is_exact rows bounds computed transfer).mpr safe
      exact crossed (le_trans within.1 within.2)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source
