import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold.Reattachment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold

variable {Candidate Address : Type*}

/-- Each row is the source's spending allowance at one original address after
incumbent obligations. Concurrent draws on the same allowance share a row. -/
structure CapacityRow (Address : Type*) where
  address : Address
  fullPayment : ℚ
  available : ℚ
  full_nonnegative : 0 ≤ fullPayment
  available_nonnegative : 0 ≤ available

def CapacityRow.atRate (row : CapacityRow Address) (rate : ℚ) : ℚ :=
  rate * row.fullPayment

def CapacityRow.shortfall (row : CapacityRow Address) (rate : ℚ) : ℚ :=
  row.atRate rate - row.available

def CapacityRow.ceiling (row : CapacityRow Address) : ℚ :=
  if row.fullPayment = 0 then 1 else row.available / row.fullPayment

def CanPay (budgets : List (CapacityRow Address)) (rate : ℚ) : Prop :=
  ∀ row ∈ budgets, row.atRate rate ≤ row.available

def capacityCeiling (budgets : List (CapacityRow Address)) : ℚ :=
  budgets.foldr (fun row ceiling => min row.ceiling ceiling) 1

theorem capacityCeiling_nonnegative (budgets : List (CapacityRow Address)) :
    0 ≤ capacityCeiling budgets := by
  induction budgets with
  | nil => exact zero_le_one
  | cons row tail ih =>
    apply le_min _ ih
    unfold CapacityRow.ceiling
    split
    · exact zero_le_one
    · exact div_nonneg row.available_nonnegative row.full_nonnegative

theorem capacityCeiling_le_one (budgets : List (CapacityRow Address)) :
    capacityCeiling budgets ≤ 1 := by
  induction budgets with
  | nil => exact le_rfl
  | cons row tail ih => exact (min_le_right row.ceiling (capacityCeiling tail)).trans ih

theorem capacity_exact {budgets : List (CapacityRow Address)} {rate : ℚ} (within : rate ≤ 1) :
    CanPay budgets rate ↔ rate ≤ capacityCeiling budgets := by
  have perRow (row : CapacityRow Address) :
      row.atRate rate ≤ row.available ↔ rate ≤ row.ceiling := by
    by_cases zero : row.fullPayment = 0
    · simp [CapacityRow.atRate, CapacityRow.ceiling, zero, row.available_nonnegative, within]
    · have positive := lt_of_le_of_ne row.full_nonnegative (Ne.symm zero)
      rw [CapacityRow.ceiling, if_neg zero, le_div_iff₀ positive, CapacityRow.atRate]
  induction budgets with
  | nil => simp [CanPay, capacityCeiling, within]
  | cons row tail ih =>
    change (∀ other ∈ row :: tail, other.atRate rate ≤ other.available) ↔
      rate ≤ min row.ceiling (capacityCeiling tail)
    rw [List.forall_mem_cons, perRow, le_min_iff]
    exact and_congr Iff.rfl ih

private theorem capacityCeiling_attained (budgets : List (CapacityRow Address))
    (binding : capacityCeiling budgets < 1) :
    ∃ row ∈ budgets, row.ceiling = capacityCeiling budgets := by
  induction budgets with
  | nil => exact False.elim ((lt_irrefl (1 : ℚ)) binding)
  | cons row tail ih =>
    change min row.ceiling (capacityCeiling tail) < 1 at binding
    by_cases earlier : row.ceiling ≤ capacityCeiling tail
    · exact ⟨row, List.mem_cons_self, (min_eq_left earlier).symm⟩
    · have later := (lt_of_not_ge earlier).le
      rw [min_eq_right later] at binding
      obtain ⟨binds, member, tight⟩ := ih binding
      exact ⟨binds, List.mem_cons_of_mem row member, tight.trans (min_eq_right later).symm⟩

theorem capacity_binding {budgets : List (CapacityRow Address)}
    (binding : capacityCeiling budgets < 1) :
    ∃ row ∈ budgets, 0 < row.fullPayment ∧
      row.atRate (capacityCeiling budgets) = row.available := by
  obtain ⟨row, member, tight⟩ := capacityCeiling_attained budgets binding
  have nonzero : row.fullPayment ≠ 0 := by
    intro zero
    simp [CapacityRow.ceiling, zero] at tight
    exact (ne_of_lt binding) tight.symm
  have positive := lt_of_le_of_ne row.full_nonnegative (Ne.symm nonzero)
  refine ⟨row, member, positive, ?_⟩
  rw [← tight, CapacityRow.atRate, CapacityRow.ceiling, if_neg nonzero, div_mul_cancel₀ _ nonzero]

inductive CapacityDecision (budgets : List (CapacityRow Address)) (rate : ℚ) where
  | fits (allowed : CanPay budgets rate)
  | short (row : CapacityRow Address) (member : row ∈ budgets)
      (missing : 0 < row.shortfall rate)

def checkCapacity (budgets : List (CapacityRow Address)) (rate : ℚ) :
    CapacityDecision budgets rate :=
  let violates (row : CapacityRow Address) := decide (0 < row.shortfall rate)
  match found : budgets.find? violates with
  | none => .fits (by
      intro row member
      have clear := List.find?_eq_none.mp found row member
      simpa [violates, CapacityRow.shortfall] using clear)
  | some row => .short row (List.mem_of_find?_eq_some found)
      (of_decide_eq_true (List.find?_some (p := violates) found))

/-- This is the exact interval once the source identifies its paid alternatives
with the allowance checks on admissible rates. -/
theorem joint_interval {rows : List (Row Candidate)} (minimum : Minimum rows)
    (budgets : List (CapacityRow Address)) (sourceCanPay : ℚ → Prop)
    (source_exact : ∀ rate, 0 ≤ rate → rate ≤ 1 → (sourceCanPay rate ↔ CanPay budgets rate))
    (rate : ℚ) :
    (0 ≤ rate ∧ rate ≤ 1 ∧ sourceCanPay rate ∧ Eliminates rows rate) ↔
      minimum.rate ≤ rate ∧ rate ≤ capacityCeiling budgets := by
  constructor
  · rintro ⟨nonnegative, within, paid, safe⟩
    exact ⟨(minimum.exact_range rate nonnegative).mp safe,
      (capacity_exact within).mp ((source_exact rate nonnegative within).mp paid)⟩
  · rintro ⟨lower, upper⟩
    have nonnegative := minimum.nonnegative.trans lower
    have within := upper.trans (capacityCeiling_le_one budgets)
    exact ⟨nonnegative, within,
      (source_exact rate nonnegative within).mpr ((capacity_exact within).mpr upper),
      (minimum.exact_range rate nonnegative).mpr lower⟩

theorem source_minimum_or_named_shortage {rows : List (Row Candidate)} (minimum : Minimum rows)
    (budgets : List (CapacityRow Address)) (sourceCanPay : ℚ → Prop)
    (source_exact : ∀ rate, 0 ≤ rate → rate ≤ 1 → (sourceCanPay rate ↔ CanPay budgets rate)) :
    (sourceCanPay minimum.rate ∧ Eliminates rows minimum.rate) ∨
      ∃ row ∈ budgets, 0 < row.shortfall minimum.rate ∧
        ∀ rate, 0 ≤ rate → rate ≤ 1 → Eliminates rows rate → ¬ sourceCanPay rate := by
  cases checkCapacity budgets minimum.rate with
  | fits allowed =>
    exact Or.inl ⟨(source_exact minimum.rate minimum.nonnegative minimum.within).mpr allowed,
      minimum.eliminates⟩
  | short row member missing =>
    refine Or.inr ⟨row, member, missing, ?_⟩
    intro rate nonnegative within safe paid
    have lower := (minimum.exact_range rate nonnegative).mp safe
    have ordered : row.atRate minimum.rate ≤ row.atRate rate :=
      mul_le_mul_of_nonneg_right lower row.full_nonnegative
    have affordable := (source_exact rate nonnegative within).mp paid row member
    exact (not_lt_of_ge (ordered.trans affordable)) (sub_pos.mp missing)

theorem strict_source_rate_exists_iff_at_ceiling {rows : List (Row Candidate)}
    (budgets : List (CapacityRow Address)) (sourceCanPay : ℚ → Prop)
    (source_exact : ∀ rate, 0 ≤ rate → rate ≤ 1 → (sourceCanPay rate ↔ CanPay budgets rate)) :
    (∃ rate, 0 ≤ rate ∧ rate ≤ 1 ∧ sourceCanPay rate ∧ (∀ row ∈ rows, row.atRate rate < 0)) ↔
      ∀ row ∈ rows, row.atRate (capacityCeiling budgets) < 0 := by
  constructor
  · rintro ⟨rate, nonnegative, within, paid, strict⟩ row member
    have upper := (capacity_exact within).mp ((source_exact rate nonnegative within).mp paid)
    exact (row.atRate_antitone upper).trans_lt (strict row member)
  · intro strict
    have nonnegative := capacityCeiling_nonnegative budgets
    have within := capacityCeiling_le_one budgets
    exact ⟨_, nonnegative, within,
      (source_exact _ nonnegative within).mpr ((capacity_exact within).mpr le_rfl), strict⟩

theorem strict_source_rate_exists_iff {rows : List (Row Candidate)} (minimum : Minimum rows)
    (positive : 0 < minimum.rate) (budgets : List (CapacityRow Address))
    (sourceCanPay : ℚ → Prop)
    (source_exact : ∀ rate, 0 ≤ rate → rate ≤ 1 → (sourceCanPay rate ↔ CanPay budgets rate)) :
    (∃ rate, 0 ≤ rate ∧ rate ≤ 1 ∧ sourceCanPay rate ∧ (∀ row ∈ rows, row.atRate rate < 0)) ↔
      minimum.rate < capacityCeiling budgets ∧
        (∀ row ∈ rows, row.shift = 0 → row.margin < 0) :=
  (strict_source_rate_exists_iff_at_ceiling budgets sourceCanPay source_exact).trans
    (strict_after_positive_minimum minimum positive (capacityCeiling_nonnegative budgets))

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold
