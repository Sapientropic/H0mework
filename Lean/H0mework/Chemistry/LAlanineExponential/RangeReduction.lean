import H0mework.Chemistry.LAlanineExponential.Taylor

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceExponential

def lowerSequence (x : ℚ) : ℕ → ℚ
  | 0 => initialLower x
  | n + 1 => roundDown (lowerSequence x n ^ 2)

def upperSequence (x : ℚ) : ℕ → ℚ
  | 0 => initialUpper x
  | n + 1 => roundUp (upperSequence x n ^ 2)

def reducedArgument (x : ℚ) (k : ℕ) : ℚ := x / 2 ^ k
def leafLower (x : ℚ) (k : ℕ) : ℚ := lowerSequence (reducedArgument x k) k
def leafUpper (x : ℚ) (k : ℕ) : ℚ := upperSequence (reducedArgument x k) k

theorem square_contains (x : ℝ) (lo hi : ℚ)
    (nonnegative : 0 ≤ lo) (lower : (lo : ℝ) ≤ Real.exp x) (upper : Real.exp x ≤ (hi : ℝ)) :
    0 ≤ roundDown (lo ^ 2) ∧
      (roundDown (lo ^ 2) : ℝ) ≤ Real.exp (2 * x) ∧
        Real.exp (2 * x) ≤ (roundUp (hi ^ 2) : ℝ) := by
  have loNonneg : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast nonnegative
  have hiNonneg : (0 : ℝ) ≤ (hi : ℝ) := (Real.exp_pos x).le.trans upper
  have expSquare : Real.exp (2 * x) = Real.exp x ^ 2 := by rw [two_mul, Real.exp_add, pow_two]
  have lowerSquare : (lo : ℝ) ^ 2 ≤ Real.exp x ^ 2 := by
    simpa only [pow_two] using mul_le_mul lower lower loNonneg (Real.exp_pos x).le
  have upperSquare : Real.exp x ^ 2 ≤ (hi : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul upper upper (Real.exp_pos x).le hiNonneg
  refine ⟨roundDown_nonnegative _ (sq_nonneg lo), ?_, ?_⟩
  · rw [expSquare]
    have hr : (roundDown (lo ^ 2) : ℝ) ≤ (lo : ℝ) ^ 2 := by
      have hq := roundDown_le (lo ^ (2 : ℕ))
      exact_mod_cast hq
    exact hr.trans lowerSquare
  · rw [expSquare]
    have hr : (hi : ℝ) ^ 2 ≤ (roundUp (hi ^ 2) : ℝ) := by
      have hq := le_roundUp (hi ^ (2 : ℕ))
      exact_mod_cast hq
    exact upperSquare.trans hr

theorem sequence_contains (x : ℚ) (small : |x| ≤ 1 / 2) (k : ℕ) :
    0 ≤ lowerSequence x k ∧
      (lowerSequence x k : ℝ) ≤ Real.exp ((2 : ℝ) ^ k * (x : ℝ)) ∧
        Real.exp ((2 : ℝ) ^ k * (x : ℝ)) ≤ (upperSequence x k : ℝ) := by
  induction k with
  | zero => simpa only [lowerSequence, upperSequence, pow_zero, one_mul] using initial_contains x small
  | succ k ih =>
      have h := square_contains ((2 : ℝ) ^ k * (x : ℝ)) (lowerSequence x k) (upperSequence x k)
        ih.1 ih.2.1 ih.2.2
      have he : (2 : ℝ) * (2 ^ k * (x : ℝ)) = 2 ^ (k + 1) * (x : ℝ) := by
        rw [pow_succ]
        ring
      simpa only [lowerSequence, upperSequence, he] using h

theorem leaf_contains (x : ℚ) (k : ℕ) (small : |reducedArgument x k| ≤ 1 / 2) :
    0 ≤ leafLower x k ∧
      (leafLower x k : ℝ) ≤ Real.exp (x : ℝ) ∧ Real.exp (x : ℝ) ≤ (leafUpper x k : ℝ) := by
  have h := sequence_contains (reducedArgument x k) small k
  have he : (2 : ℝ) ^ k * (reducedArgument x k : ℝ) = (x : ℝ) := by
    simp only [reducedArgument, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    field_simp
  simpa only [leafLower, leafUpper, he] using h

theorem interval_contains (lo hi : ℚ) (leftSteps rightSteps : ℕ)
    (leftSmall : |reducedArgument lo leftSteps| ≤ 1 / 2)
    (rightSmall : |reducedArgument hi rightSteps| ≤ 1 / 2)
    (x : ℝ) (lower : (lo : ℝ) ≤ x) (upper : x ≤ (hi : ℝ)) :
    (leafLower lo leftSteps : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (leafUpper hi rightSteps : ℝ) := by
  exact ⟨(leaf_contains lo leftSteps leftSmall).2.1.trans (Real.exp_le_exp.mpr lower),
    (Real.exp_le_exp.mpr upper).trans (leaf_contains hi rightSteps rightSmall).2.2⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceExponential
