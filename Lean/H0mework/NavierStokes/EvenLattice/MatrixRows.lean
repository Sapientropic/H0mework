import H0mework.NavierStokes.EvenLattice.Tail

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.EvenGram

open scoped BigOperators
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore

noncomputable section

def quadratic (k : IntegerWavevector) (v : Fin 3 → Real) : Real :=
  (integerWaveNormSq k * (∑ i : Fin 3, v i ^ 2) - (∑ i : Fin 3, (k i : Real) * v i) ^ 2) /
    integerWaveNormSq k ^ 3

theorem quadratic_nonneg (k : IntegerWavevector) (v : Fin 3 → Real) : 0 ≤ quadratic k v := by
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun i => (k i : Real)) v
  apply div_nonneg (sub_nonneg.mpr cauchy) (pow_nonneg (integerWaveNormSq_nonneg k) _)

def crossDenominator (x y z : ℤ) : Real := (4 * (x : Real) ^ 2 + (y : Real) ^ 2 + (z : Real) ^ 2) ^ 3

theorem quadratic_expand (z : Lattice) (v : Fin 3 → Real) :
    quadratic (wave z) v = (∑ i : Fin 3, diagonal z i * v i ^ 2) -
      4 * v 0 * v 1 * ((z.1 : Real) * z.2.1 / crossDenominator z.1 z.2.1 z.2.2) -
      4 * v 0 * v 2 * ((z.1 : Real) * z.2.2 / crossDenominator z.1 z.2.1 z.2.2) -
      2 * v 1 * v 2 * ((z.2.1 : Real) * z.2.2 / crossDenominator z.1 z.2.1 z.2.2) := by
  simp [quadratic, wave, integerWaveNormSq, Fin.sum_univ_three, diagonal, numerator,
    squaredRadius, crossDenominator, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  ring

theorem sum_symmetric_odd (n : Nat) (f : ℤ → Real) (odd : ∀ z, f (-z) = -f z) :
    (∑ z ∈ Finset.Icc (-(n : ℤ)) n, f z) = 0 := by
  have same : (∑ z ∈ Finset.Icc (-(n : ℤ)) n, f z) =
      ∑ z ∈ Finset.Icc (-(n : ℤ)) n, -f z := by
    apply Finset.sum_bij (fun z _ => -z)
    · intro z hz
      simp only [Finset.mem_Icc] at hz ⊢
      omega
    · intro a _ b _ same
      omega
    · intro z hz
      refine ⟨-z, ?_, by simp⟩
      simp only [Finset.mem_Icc] at hz ⊢
      omega
    · intro z _
      simp [odd]
  rw [Finset.sum_neg_distrib] at same
  linarith

theorem cube_sum_zero_of_odd_first (a b : Nat) (f : Lattice → Real)
    (odd : ∀ x y z, f (-x, y, z) = -f (x, y, z)) : (∑ z ∈ cube a b, f z) = 0 := by
  simp only [cube, Finset.sum_product]
  apply sum_symmetric_odd
  intro x
  simp only [odd, Finset.sum_neg_distrib]

theorem cube_sum_zero_of_odd_last (a b : Nat) (f : Lattice → Real)
    (odd : ∀ x y z, f (x, y, -z) = -f (x, y, z)) : (∑ z ∈ cube a b, f z) = 0 := by
  simp only [cube, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  exact sum_symmetric_odd b (fun z => f (x, y, z)) (odd x y)

theorem cube_quadratic_eq_diagonal (a b : Nat) (v : Fin 3 → Real) :
    (∑ z ∈ cube a b, quadratic (wave z) v) =
      ∑ i : Fin 3, (∑ z ∈ cube a b, diagonal z i) * v i ^ 2 := by
  have xy : (∑ z ∈ cube a b, (z.1 : Real) * z.2.1 / crossDenominator z.1 z.2.1 z.2.2) = 0 := by
    apply cube_sum_zero_of_odd_first
    intro x y z
    simp [crossDenominator, neg_div]
  have xz : (∑ z ∈ cube a b, (z.1 : Real) * z.2.2 / crossDenominator z.1 z.2.1 z.2.2) = 0 := by
    apply cube_sum_zero_of_odd_last
    intro x y z
    simp [crossDenominator, neg_div]
  have yz : (∑ z ∈ cube a b, (z.2.1 : Real) * z.2.2 / crossDenominator z.1 z.2.1 z.2.2) = 0 := by
    apply cube_sum_zero_of_odd_last
    intro x y z
    simp [crossDenominator, neg_div]
  simp_rw [quadratic_expand]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, xy, xz, yz, mul_zero, sub_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

end
end SaturationMonoid.NavierStokes.EvenGram
