import H0mework.NavierStokes.EvenLattice.MatrixRows

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.EvenGram

open scoped BigOperators
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore

noncomputable section

theorem finite_lattice_quadratic_le (s : Finset Lattice) (v : Fin 3 → Real) :
    (∑ z ∈ s, quadratic (wave z) v) ≤ (63 / 8) * (∑ i : Fin 3, v i ^ 2) := by
  obtain ⟨n, large, included⟩ := exists_cube s
  calc
    _ ≤ ∑ z ∈ cube n (2 * n), quadratic (wave z) v :=
      Finset.sum_le_sum_of_subset_of_nonneg included (fun z _ _ => quadratic_nonneg (wave z) v)
    _ = ∑ i : Fin 3, (∑ z ∈ cube n (2 * n), diagonal z i) * v i ^ 2 :=
      cube_quadratic_eq_diagonal n (2 * n) v
    _ ≤ ∑ i : Fin 3, (787 / 100) * v i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (finite_diagonal_le _ i) (sq_nonneg _)
    _ = (787 / 100) * (∑ i : Fin 3, v i ^ 2) := (Finset.mul_sum ..).symm
    _ ≤ (63 / 8) * (∑ i : Fin 3, v i ^ 2) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

def parameters (k : IntegerWavevector) : Lattice := (k 0 / 2, k 1, k 2)

theorem wave_parameters (k : IntegerWavevector) (even : 2 ∣ k 0) : wave (parameters k) = k := by
  have first : 2 * (k 0 / 2) = k 0 := by omega
  funext i
  fin_cases i <;> simp [wave, parameters, first]

theorem finite_quadratic_le_raw (modes : Finset IntegerWavevector)
    (even : ∀ k ∈ modes, 2 ∣ k 0) (v : Fin 3 → Real) :
    (∑ k ∈ modes, quadratic k v) ≤ (63 / 8) * (∑ i : Fin 3, v i ^ 2) := by
  have injective : ∀ a ∈ modes, ∀ b ∈ modes, parameters a = parameters b → a = b := by
    intro a ha b hb same
    have mapped := congrArg wave same
    rwa [wave_parameters a (even a ha), wave_parameters b (even b hb)] at mapped
  calc
    _ = ∑ k ∈ modes, quadratic (wave (parameters k)) v := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [wave_parameters k (even k hk)]
    _ = ∑ z ∈ modes.image parameters, quadratic (wave z) v :=
      (Finset.sum_image (f := fun z => quadratic (wave z) v) injective).symm
    _ ≤ _ := finite_lattice_quadratic_le _ v

/-- The complete transverse vector Gram, tested on any actual real direction.
No scalar velocity majorant or cutoff-dependent constant appears. -/
theorem finite_quadratic_le (modes : Finset IntegerWavevector)
    (even : ∀ k ∈ modes, 2 ∣ k 0) (v : PhysicalSpace) :
    (∑ k ∈ modes,
      (integerWaveNormSq k * ‖v‖ ^ 2 - (∑ i : Fin 3, (k i : Real) * v i) ^ 2) /
        integerWaveNormSq k ^ 3) ≤ (63 / 8) * ‖v‖ ^ 2 := by
  simpa only [quadratic, EuclideanSpace.real_norm_sq_eq] using
    finite_quadratic_le_raw modes even (fun i => v i)

theorem whole_lattice_quadratic_le (v : PhysicalSpace) :
    (∑' z : Lattice,
      (integerWaveNormSq (wave z) * ‖v‖ ^ 2 - (∑ i : Fin 3, (wave z i : Real) * v i) ^ 2) /
        integerWaveNormSq (wave z) ^ 3) ≤ (63 / 8) * ‖v‖ ^ 2 := by
  simpa only [quadratic, EuclideanSpace.real_norm_sq_eq] using
    Real.tsum_le_of_sum_le (fun z => quadratic_nonneg (wave z) (fun i => v i))
      (fun s => finite_lattice_quadratic_le s (fun i => v i))

end
end SaturationMonoid.NavierStokes.EvenGram
