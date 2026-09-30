import H0mework.Versions.X.NavierStokes.HigherTreeSextic.LatticePower

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticLatticeTail
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeUnheatedClockMomentKernel NativeUnheatedRieszKernel NativeUnheatedSexticLatticePower
noncomputable section

theorem density_three_upper (radius : ℕ) (positive : 0 < radius) (wave : IntegerWavevector)
    (lower : (radius : ℝ)^2 ≤ mass wave) :
    density 3 wave ≤ ((radius : ℝ)*Real.sqrt radius)⁻¹ := by
  have root : 0 < Real.sqrt (radius : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have cube := pow_le_pow_left₀ root.le (radical_lower radius wave lower) 3
  have identity : (Real.sqrt (radius : ℝ))^3 = (radius : ℝ)*Real.sqrt radius := by
    rw [pow_succ, Real.sq_sqrt (Nat.cast_nonneg radius)]
  simpa only [density, identity] using inv_anti₀ (pow_pos root 3) cube

theorem seven_shell (radius : ℕ) :
    (∑ wave ∈ shell radius, density 7 wave) ≤
      26*(((radius+1 : ℕ) : ℝ)*Real.sqrt (radius+1 : ℕ))⁻¹ := by
  have point (wave : IntegerWavevector) (inside : wave ∈ shell radius) :
      density 7 wave ≤ (integerWaveNormSq wave)⁻¹*
        (((radius+1 : ℕ) : ℝ)*Real.sqrt (radius+1 : ℕ))⁻¹ := by
    have frequency := shell_frequency radius wave inside
    have wavePositive : 0 < integerWaveNormSq wave := (by positivity : 0 < (((radius+1 : ℕ) : ℝ)^2)).trans_le frequency
    have first : density 4 wave ≤ (integerWaveNormSq wave)⁻¹ := by
      rw [density_four]
      exact inv_anti₀ wavePositive (by unfold mass; linarith)
    have third := density_three_upper (radius+1) (by omega) wave
      (frequency.trans (by unfold mass; linarith))
    rw [show 7 = 4+3 by omega, density_add]
    exact mul_le_mul first third (density_positive 3 wave).le (inv_nonneg.mpr wavePositive.le)
  have compared := Finset.sum_le_sum point
  rw [← Finset.sum_mul] at compared
  exact compared.trans (mul_le_mul_of_nonneg_right (shell_inverse_sum radius) (by positivity))

theorem inverse_sqrt_step (radius : ℕ) (positive : 0 < radius) :
    (((radius+1 : ℕ) : ℝ)*Real.sqrt (radius+1 : ℕ))⁻¹ ≤
      2*((Real.sqrt (radius : ℝ))⁻¹-(Real.sqrt (radius+1 : ℕ))⁻¹) := by
  let x := Real.sqrt (radius : ℝ)
  let y := Real.sqrt ((radius : ℝ)+1)
  have x0 : 0 < x := Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive)
  have y0 : 0 < y := Real.sqrt_pos.mpr (by positivity)
  have hx : x^2 = (radius : ℝ) := Real.sq_sqrt (Nat.cast_nonneg radius)
  have hy : y^2 = (radius : ℝ)+1 := Real.sq_sqrt (by positivity)
  have denominator : ((radius : ℝ)+1)*y = y^3 := by rw [← hy]; ring
  have relation : x*y^2-x*x^2 = x := by linear_combination x*(hy-hx)
  have poly := mul_nonneg (sq_nonneg (y-x)) (show 0 ≤ 2*y+x by positivity)
  have paid : x ≤ 2*(y-x)*y^2 := by nlinarith only [relation, poly]
  simp only [Nat.cast_add, Nat.cast_one]
  change (((radius : ℝ)+1)*y)⁻¹ ≤ 2*(x⁻¹-y⁻¹)
  rw [denominator, inv_eq_one_div]
  apply (div_le_iff₀ (pow_pos y0 3)).mpr
  have identity : 2*(x⁻¹-y⁻¹)*y^3 = 2*(y-x)*y^2/x := by field_simp [x0.ne', y0.ne']
  rw [identity]
  exact (le_div_iff₀ x0).mpr (by simpa only [one_mul] using paid)

theorem seven_cube_tail (radius upper : ℕ) (positive : 0 < radius) (ordered : radius ≤ upper) :
    (∑ wave ∈ integerWaveFrequencyCube upper, density 7 wave) -
      (∑ wave ∈ integerWaveFrequencyCube radius, density 7 wave) ≤
      52*((Real.sqrt (radius : ℝ))⁻¹-(Real.sqrt (upper : ℝ))⁻¹) := by
  induction upper, ordered using Nat.le_induction with
  | base => simp
  | succ upper ordered previous =>
      have split : (∑ wave ∈ integerWaveFrequencyCube (upper+1), density 7 wave) =
          (∑ wave ∈ shell upper, density 7 wave)+(∑ wave ∈ integerWaveFrequencyCube upper, density 7 wave) := by
        exact (Finset.sum_sdiff (cube_mono (Nat.le_succ upper))).symm
      have shellBound := (seven_shell upper).trans (mul_le_mul_of_nonneg_left
        (inverse_sqrt_step upper (positive.trans_le ordered)) (by norm_num : (0 : ℝ) ≤ 26))
      rw [split]
      linarith

theorem seven_tail (radius : ℕ) (positive : 0 < radius) (F : Finset IntegerWavevector) :
    (∑ wave ∈ F \ integerWaveFrequencyCube radius, density 7 wave) ≤ 52/Real.sqrt (radius : ℝ) := by
  classical
  let upper := max radius (F.sup integerWaveCoordinateRadius)
  have covered : F \ integerWaveFrequencyCube radius ⊆
      integerWaveFrequencyCube upper \ integerWaveFrequencyCube radius := by
    intro wave inside
    refine Finset.mem_sdiff.mpr ⟨?_, (Finset.mem_sdiff.mp inside).2⟩
    exact integerWave_mem_frequencyCube_of_radius_le wave upper
      ((Finset.le_sup (Finset.mem_sdiff.mp inside).1).trans (le_max_right _ _))
  have compared := Finset.sum_le_sum_of_subset_of_nonneg covered
    (fun wave _ _ => (density_positive 7 wave).le)
  have equality : (∑ wave ∈ integerWaveFrequencyCube upper \ integerWaveFrequencyCube radius, density 7 wave) =
      (∑ wave ∈ integerWaveFrequencyCube upper, density 7 wave) -
        (∑ wave ∈ integerWaveFrequencyCube radius, density 7 wave) :=
    eq_sub_of_add_eq (Finset.sum_sdiff (cube_mono (le_max_left _ _)))
  rw [equality] at compared
  have paid := compared.trans (seven_cube_tail radius upper positive (le_max_left _ _))
  exact paid.trans (by rw [div_eq_mul_inv]; nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg (upper : ℝ))])

theorem nine_point (radius : ℕ) (positive : 0 < radius) (wave : IntegerWavevector)
    (outside : wave ∉ integerWaveFrequencyCube radius) :
    density 9 wave ≤ integerWaveCriticalKernel wave*(Real.sqrt (radius : ℝ))⁻¹ := by
  have frequency := outside_square radius wave outside
  have wavePositive : 0 < integerWaveNormSq wave := (sq_pos_of_pos (Nat.cast_pos.mpr positive)).trans_le frequency
  have first : density 4 wave ≤ (integerWaveNormSq wave)⁻¹ := by
    rw [density_four]
    exact inv_anti₀ wavePositive (by unfold mass; linarith)
  have square : density 8 wave ≤ integerWaveCriticalKernel wave := by
    rw [show 8 = 4+4 by omega, density_add]
    exact (mul_le_mul first first (density_positive 4 wave).le (inv_nonneg.mpr wavePositive.le)).trans_eq
      (by unfold integerWaveCriticalKernel; ring)
  have one : density 1 wave ≤ (Real.sqrt (radius : ℝ))⁻¹ := by
    simp only [density, pow_one]
    exact inv_anti₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr positive))
      (radical_lower radius wave (frequency.trans (by unfold mass; linarith)))
  rw [show 9 = 8+1 by omega, density_add]
  exact mul_le_mul square one (density_positive 1 wave).le (integerWaveCriticalKernel_nonneg wave)

theorem nine_tail (radius : ℕ) (positive : 0 < radius) (F : Finset IntegerWavevector) :
    (∑ wave ∈ F \ integerWaveFrequencyCube radius, density 9 wave) ≤
      26/((radius : ℝ)*Real.sqrt radius) := by
  have compared := Finset.sum_le_sum (s := F \ integerWaveFrequencyCube radius)
    (fun wave inside => nine_point radius positive wave (Finset.mem_sdiff.mp inside).2)
  rw [← Finset.sum_mul] at compared
  exact compared.trans ((mul_le_mul_of_nonneg_right
    (finiteModes_integerWaveCriticalKernel_tail_le radius positive F) (by positivity)).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticLatticeTail
