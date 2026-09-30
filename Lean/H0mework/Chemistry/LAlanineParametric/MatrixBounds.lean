import H0mework.Chemistry.LAlanineParametric.IntervalLinear

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousChart

open SourceGaussianModel SourceSignedEvaluator ContinuousGradient IntervalParameterMap
open scoped BigOperators

noncomputable section

def matrixLinear (a : Fin 3 → Fin 3 → ℚ) : Point →L[ℝ] Point :=
  ContinuousLinearMap.pi (fun i => ∑ j : Fin 3, (a i j : ℝ) • ContinuousLinearMap.proj j)

theorem matrixLinear_apply (a : Fin 3 → Fin 3 → ℚ) (v : Point) (i : Fin 3) :
    matrixLinear a v i = ∑ j : Fin 3, (a i j : ℝ) * v j := by
  simp only [matrixLinear, ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem linear_apply_row (A : Point →L[ℝ] Point) (v : Point) (i : Fin 3) :
    A v i = ∑ j : Fin 3, A (Pi.single j 1) i * v j :=
  linear_apply_coordinates ((ContinuousLinearMap.proj i).comp A) v

theorem matrixLinear_single (a : Fin 3 → Fin 3 → ℚ) (i j : Fin 3) :
    matrixLinear a (Pi.single j 1) i = (a i j : ℝ) := by
  rw [matrixLinear_apply]
  classical
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same, mul_one]
  · intro k _ hkj
    simp only [Pi.single_eq_of_ne hkj, mul_zero]
  · simp

theorem matrixLinear_contains (a : Fin 3 → Fin 3 → ℚ) :
    MatrixHolds (fun i j => point (a i j)) (matrixLinear a) := by
  intro i j
  rw [matrixLinear_single]
  exact point_holds _

theorem matrixMultiply_contains (a b : MatrixPair) (A B : Point →L[ℝ] Point)
    (ha : MatrixHolds a A) (hb : MatrixHolds b B) :
    MatrixHolds (matrixMultiply a b) (A.comp B) := by
  intro i j
  change Holds _ (A (B (Pi.single j 1)) i)
  rw [linear_apply_row]
  exact dotThree_contains _ _ _ _ (ha i) (fun k => hb k j)

theorem subtract_identity_contains (a : MatrixPair) (A : Point →L[ℝ] Point)
    (ha : MatrixHolds a A) :
    MatrixHolds (fun i j => sub (a i j) (point (if i = j then 1 else 0)))
      (A - ContinuousLinearMap.id ℝ Point) := by
  intro i j
  have h := sub_holds _ _ _ _ (ha i j) (point_holds (if i = j then 1 else 0))
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, Rat.cast_one, sub_apply,
      ContinuousLinearMap.id_apply, Pi.sub_apply, Pi.single_eq_same] using h
  · simpa only [if_neg hij, Rat.cast_zero, sub_apply,
      ContinuousLinearMap.id_apply, Pi.sub_apply, Pi.single_eq_of_ne hij] using h

def magnitude (a : Pair) : ℚ := max |a.1| |a.2|

theorem magnitude_contains (a : Pair) (x : ℝ) (h : Holds a x) :
    |x| ≤ (magnitude a : ℝ) := by
  rw [abs_le]
  have ha : |(a.1 : ℝ)| ≤ (magnitude a : ℝ) := by
    exact_mod_cast le_max_left |a.1| |a.2|
  have hb : |(a.2 : ℝ)| ≤ (magnitude a : ℝ) := by
    exact_mod_cast le_max_right |a.1| |a.2|
  constructor <;> linarith [neg_abs_le (a.1 : ℝ), le_abs_self (a.2 : ℝ), h.1, h.2]

theorem matrix_norm_le (a : MatrixPair) (A : Point →L[ℝ] Point) (bound : ℚ)
    (positive : 0 ≤ bound) (h : MatrixHolds a A)
    (rows : ∀ i, (∑ j : Fin 3, magnitude (a i j)) ≤ bound) : ‖A‖ ≤ (bound : ℝ) := by
  have hb : (0 : ℝ) ≤ (bound : ℝ) := by exact_mod_cast positive
  apply ContinuousLinearMap.opNorm_le_bound A hb
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg v))).mpr
  intro i
  rw [linear_apply_row, Real.norm_eq_abs]
  calc
    |∑ j : Fin 3, A (Pi.single j 1) i * v j| ≤
        ∑ j : Fin 3, |A (Pi.single j 1) i * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 3, (magnitude (a i j) : ℝ) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hm := magnitude_contains (a i j) _ (h i j)
      exact mul_le_mul hm (norm_le_pi_norm v j) (abs_nonneg _) ((abs_nonneg _).trans hm)
    _ = (∑ j : Fin 3, (magnitude (a i j) : ℝ)) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (bound : ℝ) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast rows i) (norm_nonneg v)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.ContinuousChart
