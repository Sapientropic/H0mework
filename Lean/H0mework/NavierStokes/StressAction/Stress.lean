import H0mework.NavierStokes.SourceAction.Convolution

set_option autoImplicit false
open scoped BigOperators ENNReal Matrix

namespace SaturationMonoid.NavierStokes.NativeFullOrderStress

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeStressSource NativeFullOrderAction

noncomputable section

def energy (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, wordWeight order ceiling wave ^ 2 * complexCoordinateAmplitudeSq (velocity wave)

def dissipation (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, wordWeight order ceiling wave ^ 2 * integerWaveViscousMultiplier wave *
    complexCoordinateAmplitudeSq (velocity wave)

def power (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, wordWeight order ceiling wave ^ 2 * complexCoordinateRealInner (velocity wave)
    (nativeFluidStressDivergenceCoefficient (quadraticFlux velocity) wave)

def stressEnergy (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes, wordWeight order ceiling wave ^ 2 *
    ∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (quadraticFlux velocity wave output input)

theorem divergence_amplitude_le (stress : NativeFluidStressFourierState) (wave : IntegerWavevector) :
    complexCoordinateAmplitudeSq (nativeFluidStressDivergenceCoefficient stress wave) ≤
      integerWaveViscousMultiplier wave *
        ∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (stress wave output input) := by
  have row (output : Coordinate) :
      Complex.normSq (∑ input : Coordinate,
        complexWavevector wave input * stress wave output input) ≤
        integerWaveNormSq wave * complexCoordinateAmplitudeSq (stress wave output) := by
    have original := complexWavevector_cross_normSq wave (stress wave output)
    have positive := complexCoordinateVectorNormSq_nonneg (complexWavevector wave ⨯₃ stress wave output)
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    change Complex.normSq (complexWavevector wave ⬝ᵥ stress wave output) ≤ _
    linarith
  have total : (∑ output : Coordinate, Complex.normSq (∑ input : Coordinate,
      complexWavevector wave input * stress wave output input)) ≤
      integerWaveNormSq wave * ∑ output : Coordinate, complexCoordinateAmplitudeSq (stress wave output) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun output _ => row output
  have scaled := mul_le_mul_of_nonneg_left total (sq_nonneg (2 * Real.pi))
  simp only [complexCoordinateAmplitudeSq] at scaled
  unfold complexCoordinateAmplitudeSq nativeFluidStressDivergenceCoefficient integerWaveViscousMultiplier
  simp only [Complex.normSq_mul, Complex.normSq_I, one_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum]
  convert! scaled using 1 <;> ring

theorem power_sq_le (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) :
    power modes order ceiling velocity ^ 2 ≤
      dissipation modes order ceiling velocity * stressEnergy modes order ceiling velocity := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul modes
  · intro wave _
    exact mul_nonneg (mul_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))) (complexCoordinateAmplitudeSq_nonneg _)
  · intro wave _
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun output _ =>
      Finset.sum_nonneg fun input _ => Complex.normSq_nonneg _)
  · intro wave _
    have pairing := complexCoordinateRealInner_sq_le (velocity wave)
      (nativeFluidStressDivergenceCoefficient (quadraticFlux velocity) wave)
    have divergence := divergence_amplitude_le (quadraticFlux velocity) wave
    have combined := mul_le_mul_of_nonneg_left divergence (complexCoordinateAmplitudeSq_nonneg (velocity wave))
    have scaled := mul_le_mul_of_nonneg_left (pairing.trans combined)
      (sq_nonneg (wordWeight order ceiling wave ^ 2))
    convert scaled using 1 <;> ring

theorem energy_nonneg (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) : 0 ≤ energy modes order ceiling velocity :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _)

theorem dissipation_nonneg (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (velocity : ComplexVorticityHilbertState) : 0 ≤ dissipation modes order ceiling velocity :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))) (complexCoordinateAmplitudeSq_nonneg _)

theorem weighted_norm_sq (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (nonnegative : 0 ≤ ceiling) (velocity : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → velocity wave = 0) :
    ‖weighted order ceiling nonnegative (amplitude velocity)‖ ^ 2 = energy modes order ceiling velocity := by
  have original := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (weighted order ceiling nonnegative (amplitude velocity))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, weighted_apply, Real.norm_eq_abs,
    sq_abs, mul_pow, amplitude, vorticityRowAmplitude_sq,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at original
  change ‖weighted order ceiling nonnegative (amplitude velocity)‖ ^ 2 =
    ∑' wave, wordWeight order ceiling wave ^ 2 * complexCoordinateAmplitudeSq (velocity wave) at original
  rw [original]
  apply tsum_eq_sum
  intro wave absent
  simp only [supported wave absent, complexCoordinateAmplitudeSq, Pi.zero_apply,
    map_zero, Finset.sum_const_zero, mul_zero]

theorem stressEnergy_le (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (nonnegative : 0 ≤ ceiling) (velocity : ComplexVorticityHilbertState)
    (paid : Summable (amplitude velocity))
    (supported : ∀ wave, wave ∉ modes → velocity wave = 0) :
    stressEnergy modes order ceiling velocity ≤
      (6 * 2 ^ order) ^ 2 * (∑' wave, amplitude velocity wave) ^ 2 * energy modes order ceiling velocity := by
  have each (output input : Coordinate) :
      (∑ wave ∈ modes, wordWeight order ceiling wave ^ 2 *
        Complex.normSq (quadraticFlux velocity wave output input)) ≤
        (2 * 2 ^ order) ^ 2 * (∑' wave, amplitude velocity wave) ^ 2 * energy modes order ceiling velocity := by
    have localBound := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
      (weightedFlux order ceiling nonnegative velocity paid output input) modes
    have globalBound := weightedFlux_norm_le order ceiling nonnegative velocity paid output input
    have globalSquared := pow_le_pow_left₀ (norm_nonneg _) globalBound 2
    rw [mul_pow, mul_pow, weighted_norm_sq modes order ceiling nonnegative velocity supported] at globalSquared
    apply le_trans _ globalSquared
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weightedFlux, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, Complex.normSq_eq_norm_sq] using localBound
  have reordered : stressEnergy modes order ceiling velocity =
      ∑ output : Coordinate, ∑ input : Coordinate,
        ∑ wave ∈ modes, wordWeight order ceiling wave ^ 2 *
          Complex.normSq (quadraticFlux velocity wave output input) := by
    unfold stressEnergy
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro output _
    rw [Finset.sum_comm]
  rw [reordered]
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ => each output input
  apply bound.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem power_bound (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (nonnegative : 0 ≤ ceiling) (velocity : ComplexVorticityHilbertState)
    (paid : Summable (amplitude velocity))
    (supported : ∀ wave, wave ∉ modes → velocity wave = 0) :
    |power modes order ceiling velocity| ≤
      (6 * 2 ^ order) * (∑' wave, amplitude velocity wave) *
        Real.sqrt (energy modes order ceiling velocity) *
          Real.sqrt (dissipation modes order ceiling velocity) := by
  have majorantNonneg : 0 ≤ ∑' wave, amplitude velocity wave :=
    tsum_nonneg (vorticityRowAmplitude_nonneg velocity)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs]
  calc
    _ ≤ dissipation modes order ceiling velocity *
        ((6 * 2 ^ order) ^ 2 * (∑' wave, amplitude velocity wave) ^ 2 * energy modes order ceiling velocity) :=
      (power_sq_le modes order ceiling velocity).trans
        (mul_le_mul_of_nonneg_left (stressEnergy_le modes order ceiling nonnegative velocity paid supported)
          (dissipation_nonneg modes order ceiling velocity))
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (energy_nonneg modes order ceiling velocity),
        Real.sq_sqrt (dissipation_nonneg modes order ceiling velocity)]
      ring

theorem power_young (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (nonnegative : 0 ≤ ceiling) (velocity : ComplexVorticityHilbertState)
    (paid : Summable (amplitude velocity))
    (supported : ∀ wave, wave ∉ modes → velocity wave = 0)
    (nu : ℝ) (nuPositive : 0 < nu) :
    2 * power modes order ceiling velocity - nu * dissipation modes order ceiling velocity ≤
      ((6 * 2 ^ order) ^ 2 / nu) * (∑' wave, amplitude velocity wave) ^ 2 *
        energy modes order ceiling velocity := by
  let a := (6 * 2 ^ order) * (∑' wave, amplitude velocity wave) *
    Real.sqrt (energy modes order ceiling velocity)
  let b := Real.sqrt (dissipation modes order ceiling velocity)
  have bound : power modes order ceiling velocity ≤ a * b :=
    (le_abs_self _).trans (power_bound modes order ceiling nonnegative velocity paid supported)
  have bSquare : b ^ 2 = dissipation modes order ceiling velocity :=
    Real.sq_sqrt (dissipation_nonneg modes order ceiling velocity)
  have aSquare : a ^ 2 = (6 * 2 ^ order) ^ 2 * (∑' wave, amplitude velocity wave) ^ 2 *
      energy modes order ceiling velocity := by
    dsimp [a]
    rw [mul_pow, mul_pow, Real.sq_sqrt (energy_nonneg modes order ceiling velocity)]
  have young : 2 * power modes order ceiling velocity - nu * dissipation modes order ceiling velocity ≤
      a ^ 2 / nu := by
    apply (le_div_iff₀ nuPositive).mpr
    have square := sq_nonneg (a - nu * b)
    rw [sub_sq, mul_pow nu b, bSquare] at square
    have scaled := mul_le_mul_of_nonneg_left bound nuPositive.le
    nlinarith
  apply young.trans_eq
  rw [aSquare]
  ring

theorem power_absorbed (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (nonnegative : 0 ≤ ceiling) (velocity : ComplexVorticityHilbertState)
    (paid : Summable (amplitude velocity))
    (supported : ∀ wave, wave ∉ modes → velocity wave = 0)
    (nu : ℝ) (nuPositive : 0 < nu) :
    2 * power modes order ceiling velocity - 2 * nu * dissipation modes order ceiling velocity ≤
      ((6 * 2 ^ order) ^ 2 / nu) * (∑' wave, amplitude velocity wave) ^ 2 *
        energy modes order ceiling velocity := by
  have paidPower := power_young modes order ceiling nonnegative velocity paid supported nu nuPositive
  have dissipative := mul_nonneg nuPositive.le (dissipation_nonneg modes order ceiling velocity)
  linarith

end
end SaturationMonoid.NavierStokes.NativeFullOrderStress
