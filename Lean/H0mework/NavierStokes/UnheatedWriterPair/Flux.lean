import H0mework.NavierStokes.UnheatedWriterPair.Kernel

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairInverseFlux

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeHigherTimeJets NativeCompleteStressCarrier NativeUnheatedStressPairEvolution
open NativeUnheatedPairInverseKernel

noncomputable section
variable {nu : Viscosity}

def rowBudget (nu : Viscosity) (order : ℕ) (wave : IntegerWavevector) : ℝ :=
  (scale nu)⁻¹ ^ order * weight wave ^ order

theorem rowBudget_nonnegative (order : ℕ) (wave : IntegerWavevector) : 0 ≤ rowBudget nu order wave := by
  unfold rowBudget
  positivity [scale_positive (nu := nu), weight_pos wave]

theorem kernel_bound (order : ℕ) (wave first : IntegerWavevector) :
    ((decay nu first (wave-first))⁻¹) ^ order ≤ rowBudget nu order wave := by
  have joined : first + (wave-first) = wave := by abel
  simpa only [joined, rowBudget] using inverse_power_bound (nu := nu) order first (wave-first)

theorem kernel_nonnegative (order : ℕ) (wave first : IntegerWavevector) :
    0 ≤ ((decay nu first (wave-first))⁻¹) ^ order := by
  unfold decay integerWaveViscousMultiplier
  positivity [nu.coeff_pos, integerWaveNormSq_nonneg first, integerWaveNormSq_nonneg (wave-first)]

def coefficient (nu : Viscosity) (order : ℕ) (left right : ComplexVorticityHilbertState) :
    NativeFluidStressFourierState := fun wave output input =>
  -∑' first, ((decay nu first (wave-first))⁻¹) ^ order • (left first input * right (wave-first) output)

theorem pair_summable (order : ℕ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    Summable (fun first => ((decay nu first (wave-first))⁻¹) ^ order •
      (left first input * right (wave-first) output)) := by
  apply Summable.of_norm
  apply ((mixed_pair_summable left right wave output input).norm.mul_left
    (rowBudget nu order wave)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro first
  rw [norm_smul, Real.norm_of_nonneg (kernel_nonnegative order wave first)]
  exact mul_le_mul_of_nonneg_right (kernel_bound order wave first) (norm_nonneg _)

theorem coordinate_bound (state : ComplexVorticityHilbertState) (wave : IntegerWavevector)
    (coordinate : Coordinate) : ‖state wave coordinate‖ ≤ vorticityRowAmplitude state wave := by
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)

theorem absolute_pair_bound (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    (∑' first, ‖left first input * right (wave-first) output‖) ≤ 3 * ‖left‖ * ‖right‖ := by
  apply le_trans _ (tsum_fixedOutputVorticityAmplitudeProduct_le_three_mul_norm left right wave)
  apply (mixed_pair_summable left right wave output input).norm.tsum_le_tsum _
    (summable_fixedOutputVorticityAmplitudeProduct left right wave)
  intro first
  rw [norm_mul]
  exact mul_le_mul (coordinate_bound left first input) (coordinate_bound right (wave-first) output)
    (norm_nonneg _) (vorticityRowAmplitude_nonneg _ _)

theorem coefficient_bound (order : ℕ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    ‖coefficient nu order left right wave output input‖ ≤ rowBudget nu order wave * (3 * ‖left‖ * ‖right‖) := by
  rw [coefficient, norm_neg]
  apply (norm_tsum_le_tsum_norm (pair_summable order left right wave output input).norm).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (absolute_pair_bound left right wave output input)
    (rowBudget_nonnegative order wave))
  rw [← tsum_mul_left]
  apply (pair_summable order left right wave output input).norm.tsum_le_tsum _
    ((mixed_pair_summable left right wave output input).norm.mul_left (rowBudget nu order wave))
  intro first
  rw [norm_smul, Real.norm_of_nonneg (kernel_nonnegative order wave first)]
  exact mul_le_mul_of_nonneg_right (kernel_bound order wave first) (norm_nonneg _)

theorem coefficient_zero (left right : ComplexVorticityHilbertState) :
    coefficient nu 0 left right = mixedFlux left right := by
  funext wave output input
  simp only [coefficient, pow_zero, one_smul, mixedFlux]

theorem coefficient_add_left (order : ℕ) (left other right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    coefficient nu order (left + other) right wave output input =
      coefficient nu order left right wave output input + coefficient nu order other right wave output input := by
  simp only [coefficient, lp.coeFn_add, Pi.add_apply, add_mul, smul_add]
  rw [(pair_summable order left right wave output input).tsum_add
    (pair_summable order other right wave output input), neg_add]

theorem coefficient_add_right (order : ℕ) (left right other : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    coefficient nu order left (right + other) wave output input =
      coefficient nu order left right wave output input + coefficient nu order left other wave output input := by
  simp only [coefficient, lp.coeFn_add, Pi.add_apply, mul_add, smul_add]
  rw [(pair_summable order left right wave output input).tsum_add
    (pair_summable order left other wave output input), neg_add]

theorem coefficient_smul_left (order : ℕ) (scalar : ℝ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    coefficient nu order (scalar • left) right wave output input = scalar • coefficient nu order left right wave output input := by
  simp only [coefficient, lp.coeFn_smul, Pi.smul_apply, smul_mul_assoc, smul_neg]
  simp_rw [smul_comm _ scalar]
  rw [Summable.tsum_const_smul scalar (pair_summable order left right wave output input)]

theorem coefficient_smul_right (order : ℕ) (scalar : ℝ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    coefficient nu order left (scalar • right) wave output input = scalar • coefficient nu order left right wave output input := by
  simp only [coefficient, lp.coeFn_smul, Pi.smul_apply, mul_smul_comm, smul_neg]
  simp_rw [smul_comm _ scalar]
  rw [Summable.tsum_const_smul scalar (pair_summable order left right wave output input)]

def coefficientLinear (nu : Viscosity) (order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) :
    ComplexVorticityHilbertState →ₗ[ℝ] ComplexVorticityHilbertState →ₗ[ℝ] ℂ where
  toFun left :=
    { toFun right := coefficient nu order left right wave output input
      map_add' right other := coefficient_add_right order left right other wave output input
      map_smul' scalar right := coefficient_smul_right order scalar left right wave output input }
  map_add' left other := by
    ext right
    exact coefficient_add_left order left other right wave output input
  map_smul' scalar left := by
    ext right
    exact coefficient_smul_left order scalar left right wave output input

def coefficientCLM (nu : Viscosity) (order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState →L[ℝ] ℂ :=
  (coefficientLinear nu order wave output input).mkContinuous₂ (3 * rowBudget nu order wave)
    (fun left right => (coefficient_bound order left right wave output input).trans_eq (by ring))

@[simp] theorem coefficientCLM_apply (order : ℕ) (wave : IntegerWavevector) (output input : Coordinate)
    (left right : ComplexVorticityHilbertState) :
    coefficientCLM nu order wave output input left right = coefficient nu order left right wave output input := rfl

theorem moment_bound (order : ℕ) (left right : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) (output input : Coordinate) :
    (weight wave)⁻¹ ^ order * ‖coefficient nu (order+2) left right wave output input‖ ≤
      ((scale nu)⁻¹ ^ (order+2) * (3 * ‖left‖ * ‖right‖)) * weight wave ^ 2 := by
  have bounded := mul_le_mul_of_nonneg_left (coefficient_bound (nu := nu) (order+2) left right wave output input)
    (pow_nonneg (inv_nonneg.mpr (weight_pos wave).le) order)
  apply bounded.trans_eq
  rw [rowBudget, pow_add (weight wave), ← mul_assoc, ← mul_assoc]
  have cancel : (weight wave)⁻¹ ^ order * weight wave ^ order = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (weight_pos wave).ne', one_pow]
  calc
    _ = ((weight wave)⁻¹ ^ order * weight wave ^ order) *
        ((scale nu)⁻¹ ^ (order+2) * (3 * ‖left‖ * ‖right‖) * weight wave ^ 2) := by ring
    _ = _ := by rw [cancel, one_mul]

theorem moment_summable (order : ℕ) (left right : ComplexVorticityHilbertState)
    (output input : Coordinate) :
    Summable (fun wave => (weight wave)⁻¹ ^ order * ‖coefficient nu (order+2) left right wave output input‖) := by
  apply (weight_summable.mul_left ((scale nu)⁻¹ ^ (order+2) * (3 * ‖left‖ * ‖right‖))).of_nonneg_of_le
  · intro wave
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (weight_pos wave).le) order) (norm_nonneg _)
  · exact fun wave => moment_bound order left right wave output input

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairInverseFlux
