import H0mework.Versions.X.NavierStokes.SourceAction.Next
import H0mework.Versions.X.NavierStokes.SourceAction.Synthesis

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeFullOrderFlux

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderSynthesis
open NativeFullOrderAction NativeFullOrderEvolution NativeFullOrderNext NativeStressSource

noncomputable section

def velocityMomentDensity (order : ℕ) (velocity : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (velocity wave)

theorem capped_amplitude_norm_sq_le (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (velocity : ComplexVorticityHilbertState) (paid : Summable (velocityMomentDensity order velocity)) :
    ‖weighted order ceiling nonnegative (amplitude velocity)‖ ^ 2 ≤
      ∑' wave, velocityMomentDensity order velocity wave := by
  have normEq := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (weighted order ceiling nonnegative (amplitude velocity))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at normEq
  rw [normEq]
  have capped := (lp.memℓp (weighted order ceiling nonnegative (amplitude velocity))).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at capped
  apply capped.tsum_le_tsum _ paid
  intro wave
  simp only [weighted_apply, Real.norm_eq_abs, sq_abs, mul_pow, amplitude,
    vorticityRowAmplitude_sq, velocityMomentDensity]
  apply mul_le_mul_of_nonneg_right _ (complexCoordinateVectorNormSq_nonneg _)
  apply pow_le_pow_left₀ (wordWeight_nonneg order ceiling nonnegative wave) _ 2
  exact pow_le_pow_left₀ (le_min (frequencySize_nonneg wave) nonnegative) (min_le_left _ _) order

def fluxMomentDensity (order : ℕ) (velocity : ComplexVorticityHilbertState)
    (output input : Coordinate) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * Complex.normSq (quadraticFlux velocity wave output input)

theorem flux_moment_finite_bound (order : ℕ) (velocity : ComplexVorticityHilbertState)
    (majorant : Summable (amplitude velocity)) (paid : Summable (velocityMomentDensity order velocity))
    (output input : Coordinate) (observed : Finset IntegerWavevector) :
    (∑ wave ∈ observed, fluxMomentDensity order velocity output input wave) ≤
      (2 * 2 ^ order) ^ 2 * (∑' wave, amplitude velocity wave) ^ 2 *
        (∑' wave, velocityMomentDensity order velocity wave) := by
  let ceiling := frequencyCeiling observed
  have nonnegative : 0 ≤ ceiling := frequencyCeiling_nonneg observed
  have normBound := weightedFlux_norm_le order ceiling nonnegative velocity majorant output input
  have squared := pow_le_pow_left₀ (norm_nonneg _) normBound 2
  rw [mul_pow, mul_pow] at squared
  have normBudget := squared.trans (mul_le_mul_of_nonneg_left
    (capped_amplitude_norm_sq_le order ceiling nonnegative velocity paid)
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have finite := lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
    (weightedFlux order ceiling nonnegative velocity majorant output input) observed
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at finite
  apply le_trans _ normBudget
  convert! finite using 1
  apply Finset.sum_congr rfl
  intro wave inside
  simp only [weightedFlux, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    fluxMomentDensity, Complex.normSq_eq_norm_sq]
  rw [wordWeight_full_on_modes observed order wave inside]

theorem flux_moment_control (order : ℕ) (velocity : ComplexVorticityHilbertState)
    (majorant : Summable (amplitude velocity)) (paid : Summable (velocityMomentDensity order velocity))
    (output input : Coordinate) :
    Summable (fluxMomentDensity order velocity output input) ∧
      (∑' wave, fluxMomentDensity order velocity output input wave) ≤
        (2 * 2 ^ order) ^ 2 * (∑' wave, amplitude velocity wave) ^ 2 *
          (∑' wave, velocityMomentDensity order velocity wave) := by
  have nonnegative (wave) : 0 ≤ fluxMomentDensity order velocity output input wave :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have finite := flux_moment_finite_bound order velocity majorant paid output input
  exact ⟨summable_of_sum_le nonnegative finite, Real.tsum_le_of_sum_le nonnegative finite⟩

theorem source_square_moment_eq (state : ComplexVorticityHilbertState) (order : ℕ) :
    (fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (wholeBiotSavartVelocityState state wave)) = momentDensity order state := by
  funext wave
  simp only [momentDensity, wholeBiotSavartVelocityState_apply,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, ← pow_mul, Nat.mul_comm order 2]

theorem source_amplitude_summable (state : ComplexVorticityHilbertState) (paid : MomentRegular state) :
    Summable (amplitude (wholeBiotSavartVelocityState state)) := by
  have second : Summable fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (wholeBiotSavartVelocityState state wave) := by
    rw [source_square_moment_eq]
    exact paid 2
  simpa only [pow_zero, one_mul] using summable_moment_of_square (wholeBiotSavartVelocityState state) 0 second

def sourceMajorantBudget (index : ℕ) : ℝ := (runMomentBudget 2 index + ∑' wave, decay wave) / 2

def sourceFluxBudget (order index : ℕ) : ℝ :=
  (2 * 2 ^ order) ^ 2 * sourceMajorantBudget index ^ 2 * runMomentBudget order index

theorem run_receipt_flux_control (order index : ℕ)
    (time : Set.Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (output input : Coordinate) :
    let velocity := wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time)
    Summable (fluxMomentDensity order velocity output input) ∧
      (∑' wave, fluxMomentDensity order velocity output input wave) ≤ sourceFluxBudget order index := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have regular := run_receipt_momentRegular index time
  have source order := run_receipt_moment_control order index time
  have paid : Summable (velocityMomentDensity order (wholeBiotSavartVelocityState state)) := regular order
  have sourceNorm : (∑' wave, velocityMomentDensity order (wholeBiotSavartVelocityState state) wave) ≤
      runMomentBudget order index := (source order).2
  have second : Summable fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (wholeBiotSavartVelocityState state wave) := by
    rw [source_square_moment_eq]
    exact regular 2
  have majorant : (∑' wave, amplitude (wholeBiotSavartVelocityState state) wave) ≤ sourceMajorantBudget index := by
    have original := moment_le_square_payment (wholeBiotSavartVelocityState state) 0 second
    simp only [pow_zero, one_mul, source_square_moment_eq] at original
    apply original.trans
    exact div_le_div_of_nonneg_right (add_le_add (source 2).2 le_rfl) (by norm_num)
  have majorantNonneg : 0 ≤ ∑' wave, amplitude (wholeBiotSavartVelocityState state) wave :=
    tsum_nonneg (vorticityRowAmplitude_nonneg _)
  have controlled := flux_moment_control order (wholeBiotSavartVelocityState state)
    (source_amplitude_summable state regular) paid output input
  refine ⟨controlled.1, controlled.2.trans ?_⟩
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ majorantNonneg majorant 2) (sq_nonneg _)) sourceNorm
    (tsum_nonneg fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeFullOrderFlux
