import H0mework.Versions.X.NavierStokes.PhysicalReadout.Source
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger

set_option autoImplicit false
open scoped BigOperators ENNReal Matrix

namespace SaturationMonoid.NavierStokes.NativePhysicalGradient

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativePhysicalFourier

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def multiplier (wave : IntegerWavevector) (direction : Coordinate) : ℂ :=
  Complex.I * ((2 * Real.pi : ℝ) : ℂ) * complexWavevector wave direction

theorem multiplier_norm_sq (wave : IntegerWavevector) (direction : Coordinate) :
    ‖multiplier wave direction‖ ^ 2 = (2 * Real.pi) ^ 2 * (wave direction : ℝ) ^ 2 := by
  simp only [multiplier, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    complexWavevector, Real.norm_eq_abs, mul_pow, sq_abs]

theorem multiplier_sum_norm_sq (wave : IntegerWavevector) :
    (∑ direction, ‖multiplier wave direction‖ ^ 2) =
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave := by
  simp_rw [multiplier_norm_sq]
  rw [← Finset.mul_sum]
  rfl

def coefficient (state : ComplexVorticityHilbertState) (direction output : Coordinate)
    (wave : IntegerWavevector) : ℂ :=
  multiplier wave direction * wholeBiotSavartVelocityState state wave output

theorem coefficient_sum_norm_sq (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    (∑ direction, ∑ output, ‖coefficient state direction output wave‖ ^ 2) =
      (2 * Real.pi) ^ 2 * integerWaveNormSq wave *
        complexCoordinateVectorNormSq (biotSavartVelocityCoefficient wave (state wave)) := by
  simp only [coefficient, norm_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [multiplier_sum_norm_sq]
  simp only [wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
    complexCoordinateVectorNormSq, Complex.normSq_eq_norm_sq]
  ring

theorem coefficient_sum_norm_sq_le (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    (∑ direction, ∑ output, ‖coefficient state direction output wave‖ ^ 2) ≤
      vorticityRowAmplitude state wave ^ 2 := by
  rw [coefficient_sum_norm_sq, vorticityRowAmplitude_sq]
  by_cases zero : wave = 0
  · subst wave
    simp only [integerWaveNormSq, Pi.zero_apply, Int.cast_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, zero_mul]
    exact complexCoordinateVectorNormSq_nonneg _
  · have positive : 0 < (2 * Real.pi) ^ 2 * integerWaveNormSq wave := by
      exact mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos zero)
    exact (mul_le_mul_of_nonneg_left
      (biotSavartVelocityCoefficient_normSq_le wave (state wave) zero) positive.le).trans_eq
        (mul_div_cancel₀ _ positive.ne')

theorem coefficient_sum_norm_sq_eq (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) (transverse : WholeStateTransverse state) (wave : IntegerWavevector) :
    (∑ direction, ∑ output, ‖coefficient state direction output wave‖ ^ 2) =
      vorticityRowAmplitude state wave ^ 2 := by
  rw [coefficient_sum_norm_sq, vorticityRowAmplitude_sq]
  by_cases zero : wave = 0
  · subst wave
    simp [integerWaveNormSq, zeroRow, complexCoordinateVectorNormSq]
  · rw [biotSavartVelocityCoefficient_normSq_of_transverse wave (state wave) zero (transverse wave)]
    have positive : 0 < (2 * Real.pi) ^ 2 * integerWaveNormSq wave :=
      mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos zero)
    exact mul_div_cancel₀ _ positive.ne'

theorem coefficient_sq_le (state : ComplexVorticityHilbertState) (direction output : Coordinate)
    (wave : IntegerWavevector) :
    ‖coefficient state direction output wave‖ ^ 2 ≤ vorticityRowAmplitude state wave ^ 2 := by
  apply le_trans _ (coefficient_sum_norm_sq_le state wave)
  exact (Finset.single_le_sum (fun other _ => sq_nonneg ‖coefficient state direction other wave‖)
    (Finset.mem_univ output)).trans
    (Finset.single_le_sum (fun axis _ => Finset.sum_nonneg fun other _ =>
      sq_nonneg ‖coefficient state axis other wave‖)
      (Finset.mem_univ direction))

/-- Original vorticity pays for every complete first spatial derivative sequence. -/
def sequence (state : ComplexVorticityHilbertState) (direction output : Coordinate) : ScalarSequence :=
  ⟨coefficient state direction output, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (coefficient_sq_le state direction output) (summable_vorticityRowAmplitude_sq state)⟩

def field (state : ComplexVorticityHilbertState) (direction output : Coordinate) : ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (sequence state direction output)

theorem field_fourier (state : ComplexVorticityHilbertState) (direction output : Coordinate)
    (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (field state direction output) wave =
      multiplier wave direction * biotSavartVelocityCoefficient wave (state wave) output := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact congrArg (fun sequence : ScalarSequence => sequence wave)
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.apply_symm_apply (sequence state direction output))

theorem field_norm_sq (state : ComplexVorticityHilbertState) (direction output : Coordinate) :
    ‖field state direction output‖ ^ 2 = ∑' wave, ‖coefficient state direction output wave‖ ^ 2 := by
  rw [field, LinearIsometryEquiv.norm_map]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sequence] using
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (sequence state direction output)

/-- The complete spectral gradient is uniformly paid by the original enstrophy. -/
theorem gradient_norm_sq_le (state : ComplexVorticityHilbertState) :
    (∑ direction, ∑ output, ‖field state direction output‖ ^ 2) ≤ wholeVorticityEuclideanMass state := by
  have summable (direction output : Coordinate) :
      Summable (fun wave => ‖coefficient state direction output wave‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sequence] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (sequence state direction output)).summable
  simp_rw [field_norm_sq]
  simp_rw [← Summable.tsum_finsetSum (fun output _ => summable _ output)]
  rw [← Summable.tsum_finsetSum (fun direction _ =>
    summable_sum (fun output _ => summable direction output))]
  exact Summable.tsum_le_tsum (coefficient_sum_norm_sq_le state)
    (summable_sum (fun direction _ => summable_sum (fun output _ => summable direction output)))
    (summable_vorticityRowAmplitude_sq state)

/-- The source transverse and zero-row laws make Hodge's first-order budget exact. -/
theorem gradient_norm_sq (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) (transverse : WholeStateTransverse state) :
    (∑ direction, ∑ output, ‖field state direction output‖ ^ 2) = wholeVorticityEuclideanMass state := by
  have summable (direction output : Coordinate) :
      Summable (fun wave => ‖coefficient state direction output wave‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sequence] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (sequence state direction output)).summable
  simp_rw [field_norm_sq]
  simp_rw [← Summable.tsum_finsetSum (fun output _ => summable _ output)]
  rw [← Summable.tsum_finsetSum (fun direction _ =>
    summable_sum (fun output _ => summable direction output))]
  exact tsum_congr (coefficient_sum_norm_sq_eq state zeroRow transverse)

theorem multiplier_neg (wave : IntegerWavevector) (direction : Coordinate) :
    multiplier (-wave) direction = -multiplier wave direction := by
  simp [multiplier, complexWavevector]

/-- The complete L² fields satisfy integration by parts against every Fourier character. -/
theorem field_integrationByParts (state : ComplexVorticityHilbertState)
    (direction output : Coordinate) (wave : IntegerWavevector) :
    (∫ point : Torus, UnitAddTorus.mFourier wave point * field state direction output point) =
      -(∫ point : Torus, (multiplier wave direction * UnitAddTorus.mFourier wave point) *
        scalarField (wholeBiotSavartVelocityState state) output point) := by
  calc
    _ = UnitAddTorus.mFourierCoeff (field state direction output) (-wave) := by
      simp only [UnitAddTorus.mFourierCoeff, neg_neg, smul_eq_mul]
    _ = -(multiplier wave direction * UnitAddTorus.mFourierCoeff
        (scalarField (wholeBiotSavartVelocityState state) output) (-wave)) := by
      rw [field_fourier, multiplier_neg, scalarField_fourier, neg_mul]
      rfl
    _ = _ := by
      simp only [UnitAddTorus.mFourierCoeff, neg_neg, smul_eq_mul, mul_assoc,
        integral_const_mul]

theorem field_real (state : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality state)
    (direction output : Coordinate) :
    ∀ᵐ point ∂(volume : Measure Torus), (field state direction output point).im = 0 := by
  apply NativeFourierReality.inverseFourier_im_ae_zero (sequence state direction output)
  intro wave
  change coefficient state direction output (-wave) = star (coefficient state direction output wave)
  have negEq : -wave = waveNeg wave := rfl
  rw [coefficient, coefficient, multiplier_neg, negEq,
    NativePhysicalSource.velocity_reality state reality wave]
  simp [multiplier, vectorConj, complexWavevector]

def curlField (state : ComplexVorticityHilbertState) (output : Coordinate) : ScalarField :=
  ![field state 1 2 - field state 2 1,
    field state 2 0 - field state 0 2,
    field state 0 1 - field state 1 0] output

/-- The actual full source vorticity is recovered as the curl of these L² derivatives. -/
theorem curlField_eq (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) (transverse : WholeStateTransverse state) (output : Coordinate) :
    curlField state output = scalarField state output := by
  apply (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.injective
  apply lp.ext
  funext wave
  have hodge : fourierCurlCoefficient wave (biotSavartVelocityCoefficient wave (state wave)) =
      state wave := by
    by_cases zero : wave = 0
    · subst wave
      simp [zeroRow, fourierCurlCoefficient]
    · exact fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse wave (state wave)
        zero (transverse wave)
  have actual := congrFun hodge output
  have read (direction coordinate : Coordinate) :
      (UnitAddTorus.mFourierBasis (d := Coordinate)).repr (field state direction coordinate) wave =
        coefficient state direction coordinate wave := by
    rw [UnitAddTorus.mFourierBasis_repr, field_fourier]
    rfl
  have original := scalarField_fourier state output wave
  rw [← UnitAddTorus.mFourierBasis_repr] at original
  rw [original]
  fin_cases output <;>
    simp [curlField, map_sub, read, coefficient, multiplier,
      wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient,
      fourierCurlCoefficient, cross_apply, mul_sub, mul_assoc] at actual ⊢ <;>
    exact actual

theorem receipt_gradient_norm_sq
    {nu : ThreeDimensionalPeriodicFilteredNavierStokesGenerator.Viscosity}
    {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness.WholeContinuousMildSerrinReceipt
      nu initial T) (time : Set.Icc (0 : ℝ) T) :
    (∑ direction, ∑ output, ‖field (receipt.wholePath time) direction output‖ ^ 2) =
      wholeVorticityEuclideanMass (receipt.wholePath time) :=
  gradient_norm_sq _ (receipt.wholePath_zero_row time)
    (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence.wholePath_transverse receipt time)

end
end SaturationMonoid.NavierStokes.NativePhysicalGradient
