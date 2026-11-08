import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold

variable {α : Type*}

/-- The label retains the originating alternative or cut. The affine law belongs to
comparisons in which the same alternative and its peaceful benchmark stay available. -/
structure Row (α : Type*) where
  candidate : α
  margin : ℚ
  shift : ℚ
  shift_nonnegative : 0 ≤ shift

def Row.atRate (row : Row α) (rate : ℚ) : ℚ :=
  row.margin - rate * row.shift

theorem Row.atRate_antitone (row : Row α) : Antitone row.atRate := by
  intro lower upper ordered
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right ordered row.shift_nonnegative) _

def pressure (rows : List (Row α)) (rate : ℚ) : Option ℚ :=
  (best (fun row => row.atRate rate) rows).map (fun row => row.atRate rate)

theorem pressure_exact {rows : List (Row α)} {rate value : ℚ}
    (computed : pressure rows rate = some value) :
    ∃ row ∈ rows, row.atRate rate = value ∧ ∀ other ∈ rows, other.atRate rate ≤ value := by
  cases chosen : best (fun row => row.atRate rate) rows with
  | none => simp [pressure, chosen] at computed
  | some row =>
    have ⟨member, best⟩ := best_spec chosen
    simp [pressure, chosen] at computed
    exact ⟨row, member, computed, fun other inRows => computed ▸ best other inRows⟩

def Eliminates (rows : List (Row α)) (rate : ℚ) : Prop :=
  ∀ row ∈ rows, row.atRate rate ≤ 0

theorem eliminates_at_pressure {rows : List (Row α)} {rate value : ℚ}
    (computed : pressure rows rate = some value) : Eliminates rows rate ↔ value ≤ 0 := by
  obtain ⟨row, member, reading, upper⟩ := pressure_exact computed
  constructor
  · intro h
    simpa [← reading] using h row member
  · exact fun h other inRows => (upper other inRows).trans h

/-- The finite search returns an actual member, including when a tied cut precedes it. -/
def firstViolation (rows : List (Row α)) (rate : ℚ) : Option (Row α) :=
  rows.find? fun row => decide (0 < row.atRate rate)

theorem firstViolation_spec {rows : List (Row α)} {rate : ℚ} {row : Row α}
    (found : firstViolation rows rate = some row) :
    row ∈ rows ∧ 0 < row.atRate rate := by
  refine ⟨List.mem_of_find?_eq_some found, ?_⟩
  exact of_decide_eq_true (List.find?_some (p := fun other : Row α =>
    decide (0 < other.atRate rate)) found)

theorem firstViolation_eq_none {rows : List (Row α)} {rate : ℚ} :
    firstViolation rows rate = none ↔ Eliminates rows rate := by
  rw [firstViolation, List.find?_eq_none, Eliminates]
  simp

/-- The zero shift case is discharged separately by the full-rate feasibility check. -/
def Row.breakEven (row : Row α) : ℚ :=
  max 0 (row.margin / row.shift)

private theorem Row.rate_exact (row : Row α) {rate : ℚ} (nonnegative : 0 ≤ rate)
    (full : row.atRate 1 ≤ 0) :
    row.atRate rate ≤ 0 ↔ row.breakEven ≤ rate := by
  by_cases zero : row.shift = 0
  · have margin : row.margin ≤ 0 := by simpa [Row.atRate, zero] using full
    simp [Row.atRate, Row.breakEven, zero, nonnegative, margin]
  · have positive := lt_of_le_of_ne row.shift_nonnegative (Ne.symm zero)
    rw [Row.atRate, sub_nonpos, Row.breakEven, max_le_iff, div_le_iff₀ positive]
    exact ⟨fun h => ⟨nonnegative, h⟩, And.right⟩

def leastRate (rows : List (Row α)) : ℚ :=
  rows.foldr (fun row current => max row.breakEven current) 0

private theorem leastRate_le_iff (rows : List (Row α)) {rate : ℚ} (nonnegative : 0 ≤ rate) :
    leastRate rows ≤ rate ↔ ∀ row ∈ rows, row.breakEven ≤ rate := by
  induction rows with
  | nil => simp [leastRate, nonnegative]
  | cons row rows ih =>
    change max row.breakEven (leastRate rows) ≤ rate ↔ _
    rw [max_le_iff, ih]
    simp

private theorem leastRate_nonnegative (rows : List (Row α)) : 0 ≤ leastRate rows := by
  induction rows with
  | nil => exact le_rfl
  | cons row rows ih => exact ih.trans (le_max_right row.breakEven (leastRate rows))

private theorem leastRate_attained (rows : List (Row α)) (positive : 0 < leastRate rows) :
    ∃ row ∈ rows, row.breakEven = leastRate rows := by
  induction rows with
  | nil => exact False.elim ((lt_irrefl (0 : ℚ)) positive)
  | cons head tail ih =>
    change 0 < max head.breakEven (leastRate tail) at positive
    by_cases h : leastRate tail ≤ head.breakEven
    · exact ⟨head, List.mem_cons_self, (max_eq_left h).symm⟩
    · have ordered := le_of_lt (lt_of_not_ge h)
      rw [max_eq_right ordered] at positive
      obtain ⟨row, member, binding⟩ := ih positive
      exact ⟨row, List.mem_cons_of_mem head member, binding.trans (max_eq_right ordered).symm⟩

theorem exact_upper_ray {rows : List (Row α)} (full : Eliminates rows 1)
    {rate : ℚ} (nonnegative : 0 ≤ rate) : Eliminates rows rate ↔ leastRate rows ≤ rate := by
  rw [leastRate_le_iff rows nonnegative]
  exact ⟨fun safe row member => (row.rate_exact nonnegative (full row member)).mp (safe row member),
    fun bound row member => (row.rate_exact nonnegative (full row member)).mpr (bound row member)⟩

structure Minimum (rows : List (Row α)) where
  rate : ℚ
  nonnegative : 0 ≤ rate
  within : rate ≤ 1
  eliminates : Eliminates rows rate
  exact_range : ∀ other, 0 ≤ other → (Eliminates rows other ↔ rate ≤ other)
  sharp : ∀ other, 0 ≤ other → other < rate → ∃ row ∈ rows, 0 < row.atRate other
  binding : 0 < rate → ∃ row ∈ rows, 0 < row.shift ∧ row.atRate rate = 0

def minimumWhenFull (rows : List (Row α)) (full : Eliminates rows 1) : Minimum rows where
  rate := leastRate rows
  nonnegative := leastRate_nonnegative rows
  within := (exact_upper_ray full (by decide)).mp full
  eliminates := (exact_upper_ray full (leastRate_nonnegative rows)).mpr le_rfl
  exact_range := fun _ nonnegative => exact_upper_ray full nonnegative
  sharp := by
    intro other nonnegative smaller
    cases found : firstViolation rows other with
    | none =>
      have lower := (exact_upper_ray full nonnegative).mp (firstViolation_eq_none.mp found)
      exact False.elim ((not_le_of_gt smaller) lower)
    | some row =>
      have ⟨member, strictlyPositive⟩ := firstViolation_spec found
      exact ⟨row, member, strictlyPositive⟩
  binding := by
    intro positive
    obtain ⟨row, member, eq⟩ := leastRate_attained rows positive
    have nonzero : row.shift ≠ 0 := by
      intro zero
      have : row.breakEven = 0 := by simp [Row.breakEven, zero]
      exact (ne_of_gt positive) (eq.symm.trans this)
    have shifted := lt_of_le_of_ne row.shift_nonnegative (Ne.symm nonzero)
    have ratioPositive : 0 < row.margin / row.shift := by
      have aboveZero : 0 < row.breakEven := by rwa [eq]
      change 0 < max 0 (row.margin / row.shift) at aboveZero
      simpa only [lt_max_iff, lt_irrefl, false_or] using aboveZero
    have eqRatio : row.margin / row.shift = leastRate rows :=
      (max_eq_right ratioPositive.le).symm.trans eq
    refine ⟨row, member, shifted, ?_⟩
    simp [Row.atRate, ← eqRatio, div_mul_cancel₀ _ nonzero]

inductive Reattachment (rows : List (Row α)) where
  | feasible (minimum : Minimum rows)
  | zeroShift (row : Row α) (member : row ∈ rows) (unshifted : row.shift = 0)
      (positive : 0 < row.margin)
  | fullInsufficient (row : Row α) (member : row ∈ rows) (shifted : 0 < row.shift)
      (positive : 0 < row.atRate 1)

/-- Computes a least admissible common rate or keeps an exact alternative that rules
out the entire admissible interval. -/
def solve (rows : List (Row α)) : Reattachment rows :=
  match found : firstViolation rows 1 with
  | none => .feasible (minimumWhenFull rows (firstViolation_eq_none.mp found))
  | some row =>
    have ⟨member, positive⟩ := firstViolation_spec found
    if zero : row.shift = 0 then
      .zeroShift row member zero (by simpa [Row.atRate, zero] using positive)
    else
      .fullInsufficient row member (lt_of_le_of_ne row.shift_nonnegative (Ne.symm zero)) positive

theorem full_obstruction {rows : List (Row α)} {row : Row α} (member : row ∈ rows)
    (positive : 0 < row.atRate 1) {rate : ℚ} (within : rate ≤ 1) :
    ¬ Eliminates rows rate :=
  fun safe => (not_lt_of_ge (safe row member)) (positive.trans_le (row.atRate_antitone within))

theorem admissible_rate_exists_iff_full {rows : List (Row α)} :
    (∃ rate : ℚ, 0 ≤ rate ∧ rate ≤ 1 ∧ Eliminates rows rate) ↔ Eliminates rows 1 := by
  constructor
  · rintro ⟨rate, _, within, safe⟩ row member
    exact (row.atRate_antitone within).trans (safe row member)
  · exact fun full => ⟨1, by decide, le_rfl, full⟩

theorem no_admissible_rate_exact {rows : List (Row α)} :
    (¬ ∃ rate : ℚ, 0 ≤ rate ∧ rate ≤ 1 ∧ Eliminates rows rate) ↔
      ∃ row ∈ rows,
        (row.shift = 0 ∧ 0 < row.margin) ∨ (0 < row.shift ∧ row.shift < row.margin) := by
  rw [admissible_rate_exists_iff_full]
  constructor
  · intro impossible
    cases found : firstViolation rows 1 with
    | none => exact False.elim (impossible (firstViolation_eq_none.mp found))
    | some row =>
      have ⟨member, profitable⟩ := firstViolation_spec found
      have insufficient : row.shift < row.margin := by
        simpa [Row.atRate] using profitable
      refine ⟨row, member, ?_⟩
      by_cases zero : row.shift = 0
      · exact Or.inl ⟨zero, zero ▸ insufficient⟩
      · exact Or.inr ⟨lt_of_le_of_ne row.shift_nonnegative (Ne.symm zero), insufficient⟩
  · rintro ⟨row, member, zero | insufficient⟩ safe
    · exact not_lt_of_ge (safe row member) (by simpa [Row.atRate, zero.1] using zero.2)
    · exact not_lt_of_ge (safe row member) (by simpa [Row.atRate] using insufficient.2)

theorem any_positive_unshifted_blocks_every_rate {rows : List (Row α)} {row : Row α}
    (member : row ∈ rows) (unshifted : row.shift = 0) (positive : 0 < row.margin)
    (rate : ℚ) : ¬ Eliminates rows rate := by
  intro safe
  have upper := safe row member
  rw [Row.atRate, unshifted, mul_zero, sub_zero] at upper
  exact (not_lt_of_ge upper) positive

/-- Strict peace preference also excludes ties that a rate can never change. -/
theorem strict_exclusion_exact {rows : List (Row α)} {rate : ℚ} :
    (∀ row ∈ rows, row.atRate rate < 0) ↔
      (∀ row ∈ rows, row.shift = 0 → row.margin < 0) ∧
      (∀ row ∈ rows, 0 < row.shift → row.margin / row.shift < rate) := by
  constructor
  · intro strict
    refine ⟨?_, ?_⟩
    · intro row member zero
      simpa [Row.atRate, zero] using strict row member
    · intro row member positive
      exact (div_lt_iff₀ positive).mpr (sub_neg.mp (strict row member))
  · rintro ⟨zeroRows, positiveRows⟩ row member
    by_cases zero : row.shift = 0
    · simpa [Row.atRate, zero] using zeroRows row member zero
    · have positive := lt_of_le_of_ne row.shift_nonnegative (Ne.symm zero)
      exact sub_neg.mpr ((div_lt_iff₀ positive).mp (positiveRows row member positive))

theorem strict_after_positive_minimum {rows : List (Row α)} (minimum : Minimum rows)
    (positive : 0 < minimum.rate) {rate : ℚ} (nonnegative : 0 ≤ rate) :
    (∀ row ∈ rows, row.atRate rate < 0) ↔
      minimum.rate < rate ∧ (∀ row ∈ rows, row.shift = 0 → row.margin < 0) := by
  constructor
  · intro strict
    have safe := (minimum.exact_range rate nonnegative).mp (fun row member =>
      (strict row member).le)
    refine ⟨lt_of_le_of_ne safe ?_, (strict_exclusion_exact.mp strict).1⟩
    intro same
    obtain ⟨row, member, _, tied⟩ := minimum.binding positive
    have : row.atRate rate = 0 := same ▸ tied
    exact (not_lt_of_ge this.ge) (strict row member)
  · rintro ⟨above, zeroRows⟩ row member
    by_cases zero : row.shift = 0
    · simpa [Row.atRate, zero] using zeroRows row member zero
    · have positiveShift := lt_of_le_of_ne row.shift_nonnegative (Ne.symm zero)
      have strict := sub_lt_sub_left (mul_lt_mul_of_pos_right above positiveShift) row.margin
      exact strict.trans_le (minimum.eliminates row member)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Threshold
