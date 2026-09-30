import H0mework.NavierStokes.UnheatedWriterQuartic.RieszKernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticLatticePower
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalIntegerLatticeCriticalKernel ThreeDimensionalIntegerLatticeCriticalKernelExplicitTail
open NativeCompleteStressCarrier NativeUnheatedRieszKernel
noncomputable section

def mass (wave : IntegerWavevector) : ℝ := 1+integerWaveNormSq wave

theorem mass_one (wave : IntegerWavevector) : 1 ≤ mass wave := by
  unfold mass
  linarith [integerWaveNormSq_nonneg wave]

theorem mass_positive (wave : IntegerWavevector) : 0 < mass wave := lt_of_lt_of_le (by norm_num) (mass_one wave)

def radical (wave : IntegerWavevector) : ℝ := Real.sqrt (Real.sqrt (mass wave))

theorem radical_positive (wave : IntegerWavevector) : 0 < radical wave :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mass_positive wave))

theorem radical_square (wave : IntegerWavevector) : radical wave^2 = Real.sqrt (mass wave) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem radical_fourth (wave : IntegerWavevector) : radical wave^4 = mass wave := by
  rw [show radical wave^4 = (radical wave^2)^2 by ring, radical_square, Real.sq_sqrt (mass_positive wave).le]

theorem radical_rpow (wave : IntegerWavevector) : radical wave = mass wave^(1/4 : ℝ) := by
  simp only [radical, Real.sqrt_eq_rpow, ← Real.rpow_mul (mass_positive wave).le]
  norm_num

def density (power : ℕ) (wave : IntegerWavevector) : ℝ := (radical wave^power)⁻¹

theorem density_positive (power : ℕ) (wave : IntegerWavevector) : 0 < density power wave :=
  inv_pos.mpr (pow_pos (radical_positive wave) power)

theorem density_rpow (power : ℕ) (wave : IntegerWavevector) : density power wave = mass wave^(-(power : ℝ)/4) := by
  rw [density, radical_rpow, ← Real.rpow_mul_natCast (mass_positive wave).le,
    ← Real.rpow_neg (mass_positive wave).le]
  congr 1
  ring

theorem density_four (wave : IntegerWavevector) : density 4 wave = (mass wave)⁻¹ := by
  rw [density, radical_fourth]

theorem density_four_le_weight (wave : IntegerWavevector) : density 4 wave ≤ weight wave := by
  rw [density_four]
  by_cases zero : wave = 0
  · simp [zero, mass, weight, integerWaveNormSq]
  · rw [weight, if_neg zero]
    exact inv_anti₀ (integerWaveNormSq_pos zero) (by unfold mass; linarith)

theorem density_add (first last : ℕ) (wave : IntegerWavevector) :
    density (first+last) wave = density first wave*density last wave := by
  simp only [density, pow_add, mul_inv_rev, mul_comm]

theorem density_three (wave : IntegerWavevector) : density 3 wave = density 4 wave*radical wave := by
  unfold density
  field_simp [(radical_positive wave).ne']

theorem radical_lower (radius : ℕ) (wave : IntegerWavevector) (lower : (radius : ℝ)^2 ≤ mass wave) :
    Real.sqrt radius ≤ radical wave := by
  apply Real.sqrt_le_sqrt
  exact (Real.le_sqrt (Nat.cast_nonneg radius) (mass_positive wave).le).mpr lower

theorem radical_cube_upper (radius : ℕ) (positive : 0 < radius) (wave : IntegerWavevector)
    (inside : wave ∈ integerWaveFrequencyCube radius) : radical wave ≤ 2*Real.sqrt radius := by
  have atLeast : (1 : ℝ) ≤ radius := by exact_mod_cast positive
  have upper : mass wave ≤ (2*(radius : ℝ))^2 := by
    unfold mass
    nlinarith [integerWaveNormSq_le_three_mul_radius_sq_of_mem radius wave inside]
  have first : Real.sqrt (mass wave) ≤ 2*(radius : ℝ) :=
    (Real.sqrt_le_left (by positivity)).mpr upper
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) radius)]

def radius (wave : IntegerWavevector) : ℕ := max 1 (integerWaveCoordinateRadius wave)

theorem radius_positive (wave : IntegerWavevector) : 0 < radius wave :=
  lt_of_lt_of_le (by omega) (le_max_left _ _)

theorem radius_member (wave : IntegerWavevector) : wave ∈ integerWaveFrequencyCube (radius wave) :=
  integerWave_mem_frequencyCube_of_radius_le wave _ (le_max_right _ _)

theorem radius_lower (wave : IntegerWavevector) : ((radius wave : ℕ) : ℝ)^2 ≤ mass wave := by
  by_cases zero : integerWaveCoordinateRadius wave = 0
  · simp only [radius, zero, max_eq_left (by omega : 0 ≤ (1 : ℕ)), Nat.cast_one, one_pow]
    exact mass_one wave
  · have lower : 1 ≤ integerWaveCoordinateRadius wave := by omega
    simp only [radius, max_eq_right lower]
    exact (radius_square wave).trans (by unfold mass; linarith)

theorem radius_density (wave : IntegerWavevector) :
    ((radius wave : ℝ)*Real.sqrt (radius wave))⁻¹ ≤ 4*density 3 wave := by
  have upper : mass wave ≤ (2*(radius wave : ℝ))^2 := by
    have atLeast : (1 : ℝ) ≤ radius wave := by exact_mod_cast radius_positive wave
    unfold mass
    nlinarith [integerWaveNormSq_le_three_mul_radius_sq_of_mem (radius wave) wave (radius_member wave)]
  have square : radical wave^2 ≤ 2*(radius wave : ℝ) := by
    rw [radical_square]
    exact (Real.sqrt_le_left (by positivity)).mpr upper
  have cube : radical wave^3 ≤ 4*((radius wave : ℝ)*Real.sqrt (radius wave)) := by
    calc
      _ = radical wave^2*radical wave := by ring
      _ ≤ (2*(radius wave : ℝ))*(2*Real.sqrt (radius wave)) := mul_le_mul square
        (radical_cube_upper (radius wave) (radius_positive wave) wave (radius_member wave)) (radical_positive wave).le (by positivity)
      _ = _ := by ring
  unfold density
  have positive : 0 < (radius wave : ℝ)*Real.sqrt (radius wave) :=
    mul_pos (Nat.cast_pos.mpr (radius_positive wave)) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (radius_positive wave)))
  calc
    _ = 4*(4*((radius wave : ℝ)*Real.sqrt (radius wave)))⁻¹ := by
      field_simp [positive.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos (radical_positive wave) 3) cube) (by norm_num)

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticLatticePower
