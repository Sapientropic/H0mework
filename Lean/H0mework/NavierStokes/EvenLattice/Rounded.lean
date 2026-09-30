import H0mework.NavierStokes.Fourier.IntegerLatticeCriticalKernelExplicitTail

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.EvenGram

open scoped BigOperators

def multiplicity (n : Nat) : Nat := if n = 0 then 1 else 2

def squaredRadius (a b c : Nat) : Nat := 4 * a ^ 2 + b ^ 2 + c ^ 2

def numerator (a b c : Nat) : Fin 3 → Nat :=
  ![b ^ 2 + c ^ 2, 4 * a ^ 2 + c ^ 2, 4 * a ^ 2 + b ^ 2]

/-- A fixed denominator avoids normalization of a large rational lattice sum. -/
def rounded (a b c : Nat) (i : Fin 3) : Nat :=
  1000000 * numerator a b c i / squaredRadius a b c ^ 3 + 1

def roundedCube (i : Fin 3) : Nat :=
  ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 17, ∑ c ∈ Finset.range 17,
    multiplicity a * multiplicity b * multiplicity c * rounded a b c i

theorem roundedCube_bound (i : Fin 3) : roundedCube i ≤ 7120000 := by
  fin_cases i <;> decide +kernel

theorem ratio_le_rounded (a b c : Nat) (i : Fin 3) :
    (numerator a b c i : Real) / (squaredRadius a b c : Real) ^ 3 ≤
      (rounded a b c i : Real) / 1000000 := by
  by_cases zero : squaredRadius a b c = 0
  · simp [zero, rounded]
  have positive : 0 < squaredRadius a b c ^ 3 := pow_pos (Nat.pos_of_ne_zero zero) _
  have whole := Nat.lt_mul_div_succ (1000000 * numerator a b c i) positive
  have cast : (1000000 : Real) * numerator a b c i ≤
      (squaredRadius a b c : Real) ^ 3 * rounded a b c i := by
    exact_mod_cast whole.le
  have positiveReal : 0 < (squaredRadius a b c : Real) ^ 3 := by positivity
  exact (div_le_div_iff₀ positiveReal (by norm_num : (0 : Real) < 1000000)).2 (by
    nlinarith only [cast])

theorem representative_sum_le (i : Fin 3) :
    (∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 17, ∑ c ∈ Finset.range 17,
      (multiplicity a * multiplicity b * multiplicity c : Nat) *
        ((numerator a b c i : Real) / (squaredRadius a b c : Real) ^ 3)) ≤ 178 / 25 := by
  have bound := Finset.sum_le_sum (s := Finset.range 9) fun a _ =>
    Finset.sum_le_sum (s := Finset.range 17) fun b _ =>
      Finset.sum_le_sum (s := Finset.range 17) fun c _ =>
        mul_le_mul_of_nonneg_left (ratio_le_rounded a b c i) (by positivity :
          (0 : Real) ≤ (multiplicity a * multiplicity b * multiplicity c : Nat))
  have same : (∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 17, ∑ c ∈ Finset.range 17,
      (multiplicity a * multiplicity b * multiplicity c : Nat) *
        ((rounded a b c i : Real) / 1000000)) = (roundedCube i : Real) / 1000000 := by
    simp only [roundedCube, Nat.cast_sum, Nat.cast_mul, ← mul_div_assoc, ← Finset.sum_div]
  rw [same] at bound
  have finite : (roundedCube i : Real) ≤ 7120000 := by exact_mod_cast roundedCube_bound i
  linarith

end SaturationMonoid.NavierStokes.EvenGram
