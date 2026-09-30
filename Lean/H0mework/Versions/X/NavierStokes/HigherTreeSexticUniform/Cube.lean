import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePrefix
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticeTail

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformCube
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeUnheatedSexticLatticePower NativeUnheatedSexticLatticePrefix NativeUnheatedRieszKernel NativeUnheatedClockMomentKernel
noncomputable section

theorem density_le_one (power : ℕ) (wave : IntegerWavevector) : density power wave ≤ 1 := by
  have atLeast : 1 ≤ radical wave := by
    simpa only [radical, Real.sqrt_one] using Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (mass_one wave))
  unfold density
  exact inv_le_one_of_one_le₀ (one_le_pow₀ atLeast)

theorem inverse_radius (radius : ℕ) (positive : 0 < radius) (wave : IntegerWavevector)
    (outside : wave ∉ integerWaveFrequencyCube radius) : density 2 wave ≤ (radius : ℝ)⁻¹ := by
  have lower := outside_square radius wave outside
  have root : (radius : ℝ) ≤ Real.sqrt (mass wave) :=
    (Real.le_sqrt (Nat.cast_nonneg radius) (mass_positive wave).le).mpr (lower.trans (by unfold mass; linarith))
  rw [density, radical_square]
  exact inv_anti₀ (Nat.cast_pos.mpr positive) root

theorem cube_card_bound (radius : ℕ) (positive : 0 < radius) :
    ((integerWaveFrequencyCube radius).card : ℝ) ≤ 27*(radius : ℝ)^3 := by
  rw [integerWaveFrequencyCube_card]
  push_cast
  have atLeast : (1 : ℝ) ≤ radius := by exact_mod_cast positive
  have compared := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*(radius : ℝ)+1)
    (show 2*(radius : ℝ)+1 ≤ 3*(radius : ℝ) by linarith) 3
  exact compared.trans_eq (by ring)

theorem translated_sum (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube radius, density 2 (center-wave)) ≤ 135*(radius : ℝ)^2 := by
  let cube := integerWaveFrequencyCube radius
  let near := cube.filter (fun wave => center-wave ∈ cube)
  have images : near.image (fun wave => center-wave) ⊆ cube := by
    intro wave member
    obtain ⟨original, inside, rfl⟩ := Finset.mem_image.mp member
    exact (Finset.mem_filter.mp inside).2
  have nearBound : (∑ wave ∈ near, density 2 (center-wave)) ≤ 108*(radius : ℝ)^2 := by
    rw [← Finset.sum_image (fun _ _ _ _ equal => sub_right_injective equal)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg images (fun wave _ _ => (density_positive 2 wave).le)).trans
      (prefix_two radius positive)
  have farBound : (∑ wave ∈ cube \ near, density 2 (center-wave)) ≤ 27*(radius : ℝ)^2 := by
    have rows := Finset.sum_le_sum (s := cube \ near) fun wave inside => inverse_radius radius positive (center-wave) (by
      have missing := (Finset.mem_sdiff.mp inside).2
      intro close
      exact missing (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp inside).1,close⟩))
    rw [Finset.sum_const, nsmul_eq_mul] at rows
    have finite : ((cube \ near).card : ℝ) ≤ (cube.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have paid := mul_le_mul_of_nonneg_right (finite.trans (cube_card_bound radius positive)) (inv_nonneg.mpr (Nat.cast_nonneg radius))
    exact rows.trans (paid.trans_eq (by field_simp))
  rw [← Finset.sum_sdiff (Finset.filter_subset (s := cube) (p := fun wave => center-wave ∈ cube))]
  exact (add_le_add farBound nearBound).trans_eq (by ring)

theorem annulus_bound (power : ℕ) (center : IntegerWavevector) (radius : ℕ) (positive : 0 < radius) :
    (∑ wave ∈ integerWaveFrequencyCube (4*radius) \ integerWaveFrequencyCube radius,
      density power wave*density 2 (center-wave)) ≤
        ((Real.sqrt radius)^power)⁻¹*(135*((4*radius : ℕ) : ℝ)^2) := by
  have rows (wave : IntegerWavevector) (inside : wave ∈ integerWaveFrequencyCube (4*radius) \ integerWaveFrequencyCube radius) :
      density power wave*density 2 (center-wave) ≤ ((Real.sqrt radius)^power)⁻¹*density 2 (center-wave) := by
    have lower := radical_lower radius wave ((outside_square radius wave (Finset.mem_sdiff.mp inside).2).trans (by unfold mass; linarith))
    have inverse := inv_anti₀ (pow_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)) power)
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) lower power)
    exact mul_le_mul_of_nonneg_right inverse (density_positive 2 (center-wave)).le
  have compared := Finset.sum_le_sum rows
  rw [← Finset.mul_sum] at compared
  have sub := Finset.sum_le_sum_of_subset_of_nonneg (s := integerWaveFrequencyCube (4*radius) \ integerWaveFrequencyCube radius)
    Finset.sdiff_subset (fun wave _ _ => (density_positive 2 (center-wave)).le)
  exact compared.trans (mul_le_mul_of_nonneg_left (sub.trans (translated_sum center (4*radius) (by omega))) (by positivity))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticUniformCube
