import H0mework.NavierStokes.UnheatedWriterPair.KernelBilinear
import H0mework.NavierStokes.StressNegativeOne.Inclusion

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairNegativeKernel

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeUnheatedStressPairEvolution NativeUnheatedPairInverseKernel NativeUnheatedPairInverseFlux
open NativeResolventCompactness NativeWholeH1Pairing NativeEndpointVelocityCarrier

noncomputable section
variable {nu : Viscosity}

def root (wave : IntegerWavevector) : ℝ := Real.sqrt (integerWaveViscousMultiplier wave)

theorem root_nonnegative (wave : IntegerWavevector) : 0 ≤ root wave := Real.sqrt_nonneg _

theorem root_sq (wave : IntegerWavevector) : root wave ^ 2 = integerWaveViscousMultiplier wave :=
  Real.sq_sqrt (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))

theorem root_positive (wave : IntegerWavevector) (nonzero : wave ≠ 0) : 0 < root wave :=
  Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos nonzero))

def kernel (nu : Viscosity) (first last : IntegerWavevector) : ℝ :=
  root first * root last * (decay nu first last)⁻¹

theorem kernel_nonnegative (first last : IntegerWavevector) : 0 ≤ kernel nu first last := by
  unfold kernel decay
  positivity [nu.coeff_pos, root_nonnegative first, root_nonnegative last,
    mul_nonneg (sq_nonneg (2*Real.pi)) (integerWaveNormSq_nonneg first),
    mul_nonneg (sq_nonneg (2*Real.pi)) (integerWaveNormSq_nonneg last)]

theorem kernel_bound (first last : IntegerWavevector) : kernel nu first last ≤ (2*nu.coeff)⁻¹ := by
  by_cases nonzero : first ≠ 0 ∨ last ≠ 0
  · have positive := decay_positive (nu := nu) first last nonzero
    rw [kernel, mul_inv_le_iff₀ positive]
    have roots : 2 * root first * root last ≤ integerWaveViscousMultiplier first + integerWaveViscousMultiplier last := by
      nlinarith [sq_nonneg (root first-root last), root_sq first, root_sq last]
    have half : root first * root last ≤ (integerWaveViscousMultiplier first + integerWaveViscousMultiplier last)/2 := by
      linarith
    apply half.trans_eq
    unfold decay
    field_simp [nu.coeff_pos.ne']
  · push Not at nonzero
    rcases nonzero with ⟨rfl,rfl⟩
    simp [kernel, root, integerWaveViscousMultiplier, integerWaveNormSq, nu.coeff_pos.le]

def gradedKernel (nu : Viscosity) (order : ℕ) (first last : IntegerWavevector) : ℝ :=
  kernel nu first last * ((decay nu first last)⁻¹) ^ order

theorem graded_bound (order : ℕ) (wave first : IntegerWavevector) :
    ‖gradedKernel nu order first (wave-first)‖ ≤ (2*nu.coeff)⁻¹ * rowBudget nu order wave := by
  rw [gradedKernel, norm_mul, Real.norm_of_nonneg (kernel_nonnegative first (wave-first)),
    Real.norm_of_nonneg (NativeUnheatedPairInverseFlux.kernel_nonnegative order wave first)]
  exact mul_le_mul (kernel_bound first (wave-first)) (NativeUnheatedPairInverseFlux.kernel_bound order wave first)
    (NativeUnheatedPairInverseFlux.kernel_nonnegative order wave first) (by positivity [nu.coeff_pos])

def bilinear (nu : Viscosity) (order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) : State →L[ℝ] State →L[ℝ] ℂ :=
  (NativeUnheatedPairKernelBilinear.bilinear (gradedKernel nu order) wave output input ((2*nu.coeff)⁻¹ * rowBudget nu order wave)
    (graded_bound order wave)).bilinearComp
      wholeVelocityCLM wholeVelocityCLM

theorem bilinear_apply (order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) (left right : State) :
    bilinear nu order wave output input left right = -∑' first, gradedKernel nu order first (wave-first) •
      (wholeVelocity left first input * wholeVelocity right (wave-first) output) := rfl

theorem inverse_row (value : State) (wave : IntegerWavevector) :
    wholeVelocity (inverseGradient value) wave = (root wave)⁻¹ • wholeVelocity value wave := by
  by_cases zero : wave = 0
  · subst wave
    simp [wholeVelocity_zero]
  · funext coordinate
    simp only [Pi.smul_apply, wholeVelocity_nonzero _ ⟨wave,zero⟩, inverseGradient]
    rfl

theorem bilinear_original (order : ℕ) (wave : IntegerWavevector) (output input : Coordinate) (left right : State) :
    bilinear nu order wave output input (inverseGradient left) (inverseGradient right) =
      coefficient nu (order+1) (wholeVelocity left) (wholeVelocity right) wave output input := by
  rw [bilinear_apply, coefficient]
  congr 1
  apply tsum_congr
  intro first
  by_cases leftZero : first = 0
  · subst first
    simp [wholeVelocity_zero, inverse_row]
  by_cases rightZero : wave-first = 0
  · simp [rightZero, wholeVelocity_zero, inverse_row]
  rw [inverse_row, inverse_row]
  simp only [Pi.smul_apply, Complex.real_smul, gradedKernel, kernel, pow_succ]
  push_cast
  field_simp [(root_positive first leftZero).ne', (root_positive (wave-first) rightZero).ne']

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairNegativeKernel
