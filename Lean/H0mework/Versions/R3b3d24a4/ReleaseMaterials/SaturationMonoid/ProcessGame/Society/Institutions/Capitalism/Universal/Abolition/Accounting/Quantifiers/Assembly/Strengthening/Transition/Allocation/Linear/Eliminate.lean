import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Core
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

variable {n : ℕ}

def Inequality.tail (row : Inequality (n + 1)) : Inequality n :=
  ⟨fun i => row.coeff i.succ, row.bound⟩

/-- A nonzero head coefficient turns the row into an upper or lower bound
on the eliminated variable after the remaining values have been fixed. -/
def Inequality.boundAt (row : Inequality (n + 1)) (values : Fin n → ℚ) : ℚ :=
  (row.bound - dot row.tail.coeff values) / row.coeff 0

private theorem holds_cons (row : Inequality (n + 1)) (head : ℚ) (values : Fin n → ℚ) :
    row.Holds (Fin.cons head values) ↔ row.coeff 0 * head + dot row.tail.coeff values ≤ row.bound := by
  simp only [Inequality.Holds, dot, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Inequality.tail]

theorem holds_lower (row : Inequality (n + 1)) (head : ℚ) (values : Fin n → ℚ)
    (negative : row.coeff 0 < 0) :
    row.Holds (Fin.cons head values) ↔ row.boundAt values ≤ head := by
  have positive : 0 < -row.coeff 0 := neg_pos.mpr negative
  have reversed :
      (row.bound - dot row.tail.coeff values) / row.coeff 0 =
        (dot row.tail.coeff values - row.bound) / (-row.coeff 0) := by
    rw [div_neg, ← neg_div]
    congr 1
    linarith
  rw [holds_cons, Inequality.boundAt, reversed, div_le_iff₀ positive]
  constructor
  · intro fits
    linarith only [fits]
  · intro fits
    linarith only [fits]

theorem holds_upper (row : Inequality (n + 1)) (head : ℚ) (values : Fin n → ℚ)
    (positive : 0 < row.coeff 0) :
    row.Holds (Fin.cons head values) ↔ head ≤ row.boundAt values := by
  rw [holds_cons, Inequality.boundAt, le_div_iff₀' positive, le_sub_iff_add_le]

theorem holds_zero (row : Inequality (n + 1)) (head : ℚ) (values : Fin n → ℚ)
    (zero : row.coeff 0 = 0) :
    row.Holds (Fin.cons head values) ↔ row.tail.Holds values := by
  rw [holds_cons, zero, zero_mul, zero_add]; rfl

def zeroRows (rows : List (Inequality (n + 1))) :=
  rows.filter fun row => decide (row.coeff 0 = 0)

def lowerRows (rows : List (Inequality (n + 1))) :=
  rows.filter fun row => decide (row.coeff 0 < 0)

def upperRows (rows : List (Inequality (n + 1))) :=
  rows.filter fun row => decide (0 < row.coeff 0)

@[simp] theorem mem_zeroRows {rows : List (Inequality (n + 1))} {row : Inequality (n + 1)} :
    row ∈ zeroRows rows ↔ row ∈ rows ∧ row.coeff 0 = 0 := by
  simp [zeroRows]

@[simp] theorem mem_lowerRows {rows : List (Inequality (n + 1))} {row : Inequality (n + 1)} :
    row ∈ lowerRows rows ↔ row ∈ rows ∧ row.coeff 0 < 0 := by
  simp [lowerRows]

@[simp] theorem mem_upperRows {rows : List (Inequality (n + 1))} {row : Inequality (n + 1)} :
    row ∈ upperRows rows ↔ row ∈ rows ∧ 0 < row.coeff 0 := by
  simp [upperRows]

def paired (lower upper : Inequality (n + 1)) : Inequality n where
  coeff := fun i => upper.tail.coeff i / upper.coeff 0 - lower.tail.coeff i / lower.coeff 0
  bound := upper.bound / upper.coeff 0 - lower.bound / lower.coeff 0

private theorem dot_sub (a b x : Fin n → ℚ) :
    dot (fun i => a i - b i) x = dot a x - dot b x := by
  simp only [dot, sub_mul, Finset.sum_sub_distrib]

private theorem dot_div (a x : Fin n → ℚ) (q : ℚ) :
    dot (fun i => a i / q) x = dot a x / q := by
  simp only [dot, div_mul_eq_mul_div₀, Finset.sum_div]

theorem paired_holds (lower upper : Inequality (n + 1)) (values : Fin n → ℚ) :
    (paired lower upper).Holds values ↔ lower.boundAt values ≤ upper.boundAt values := by
  simp only [Inequality.Holds, paired, dot_sub, dot_div, Inequality.boundAt, sub_div]
  constructor
  · intro fits
    linarith only [fits]
  · intro fits
    linarith only [fits]

/-- Preserve every zero row and every lower/upper pair on the remaining
coordinates. No lower or upper bound is invented when that side is empty. -/
def eliminate (rows : List (Inequality (n + 1))) : List (Inequality n) :=
  (zeroRows rows).map Inequality.tail ++
    (lowerRows rows).flatMap fun lower => (upperRows rows).map (paired lower)

theorem eliminate_keeps_pair {rows : List (Inequality (n + 1))}
    {values : Fin n → ℚ} (projected : Feasible (eliminate rows) values)
    {lower upper : Inequality (n + 1)} (low : lower ∈ lowerRows rows) (up : upper ∈ upperRows rows) :
    lower.boundAt values ≤ upper.boundAt values :=
  (paired_holds lower upper values).mp (projected _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨lower, low, List.mem_map.mpr ⟨upper, up, rfl⟩⟩)))

theorem eliminate_sound {rows : List (Inequality (n + 1))} {head : ℚ} {values : Fin n → ℚ}
    (original : Feasible rows (Fin.cons head values)) : Feasible (eliminate rows) values := by
  intro row listed
  rcases List.mem_append.mp listed with zero | pair
  · obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp zero
    obtain ⟨inRows, zeroHead⟩ := mem_zeroRows.mp oldMember
    exact (holds_zero old head values zeroHead).mp (original old inRows)
  · obtain ⟨lower, low, seen⟩ := List.mem_flatMap.mp pair
    obtain ⟨upper, up, rfl⟩ := List.mem_map.mp seen
    obtain ⟨inRowsLow, negative⟩ := mem_lowerRows.mp low
    obtain ⟨inRowsUp, positive⟩ := mem_upperRows.mp up
    exact (paired_holds lower upper values).mpr
      (((holds_lower lower head values negative).mp (original lower inRowsLow)).trans
        ((holds_upper upper head values positive).mp (original upper inRowsUp)))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
