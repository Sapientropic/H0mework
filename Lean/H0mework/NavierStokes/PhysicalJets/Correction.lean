import H0mework.NavierStokes.SourceAction.ActionMoments

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeFullOrderCorrection

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderEvolution NativeFullOrderNext NativeFullOrderFlux
open NativeFullOrderSynthesis NativeFullOrderActionMoments NativeStressSource

noncomputable section

theorem projected_velocity_eq (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    wholeBiotSavartVelocityState (complexSharpSupportProjection modes state) =
      finiteStateWholeVelocity modes state := by
  apply lp.ext
  funext wave
  by_cases inside : wave ∈ modes <;>
    simp [wholeBiotSavartVelocityState_apply, finiteStateWholeVelocity_apply,
      finiteStateVelocityCoefficient, complexSharpSupportProjection_apply, inside]

theorem projected_moment_le (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (order : ℕ) (paid : Summable (momentDensity order state)) :
    Summable (velocityMomentDensity order (finiteStateWholeVelocity modes state)) ∧
      (∑' wave, velocityMomentDensity order (finiteStateWholeVelocity modes state) wave) ≤ moment order state := by
  have pointwise (wave) : velocityMomentDensity order (finiteStateWholeVelocity modes state) wave ≤
      momentDensity order state wave := by
    by_cases inside : wave ∈ modes
    · simp only [velocityMomentDensity, momentDensity, finiteStateWholeVelocity_apply, if_pos inside, le_refl]
    · simp only [velocityMomentDensity, finiteStateWholeVelocity_apply, if_neg inside,
        complexCoordinateVectorNormSq, Pi.zero_apply, map_zero, Finset.sum_const_zero, mul_zero]
      exact momentDensity_nonneg order state wave
  have summable := paid.of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) pointwise
  exact ⟨summable, summable.tsum_le_tsum pointwise paid⟩

theorem projected_majorant_le (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState)
    (paid : MomentRegular state) :
    (∑' wave, amplitude (finiteStateWholeVelocity modes state) wave) ≤
      ∑' wave, amplitude (wholeBiotSavartVelocityState state) wave := by
  apply (finite_amplitude_summable modes state).tsum_le_tsum _ (source_amplitude_summable state paid)
  intro wave
  by_cases inside : wave ∈ modes
  · simp only [amplitude, vorticityRowAmplitude, finiteStateWholeVelocity_apply,
      wholeBiotSavartVelocityState_apply, if_pos inside, le_refl]
  · simp only [amplitude, vorticityRowAmplitude, finiteStateWholeVelocity_apply, if_neg inside,
      complexCoordinateAmplitudeSq, Pi.zero_apply, map_zero, Finset.sum_const_zero, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

theorem run_majorant_le (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    (∑' wave, amplitude (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time)) wave) ≤
      sourceMajorantBudget index := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have second : Summable fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (wholeBiotSavartVelocityState state wave) := by
    rw [source_square_moment_eq]
    exact (run_receipt_moment_control 2 index time).1
  have original := moment_le_square_payment (wholeBiotSavartVelocityState state) 0 second
  simp only [pow_zero, one_mul, source_square_moment_eq] at original
  exact original.trans (div_le_div_of_nonneg_right
    (add_le_add (run_receipt_moment_control 2 index time).2 le_rfl) (by norm_num))

theorem run_projected_flux_control (modes : Finset IntegerWavevector) (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (output input : Coordinate) :
    let velocity := finiteStateWholeVelocity modes ((run stackedShortCurrent index).receipt.wholePath time)
    Summable (fluxMomentDensity order velocity output input) ∧
      (∑' wave, fluxMomentDensity order velocity output input wave) ≤ sourceFluxBudget order index := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have regular := run_receipt_momentRegular index time
  have projected := projected_moment_le modes state order (regular order)
  have majorant := (projected_majorant_le modes state regular).trans (run_majorant_le index time)
  have majorantNonneg : 0 ≤ ∑' wave, amplitude (finiteStateWholeVelocity modes state) wave :=
    tsum_nonneg (vorticityRowAmplitude_nonneg _)
  have controlled := flux_moment_control order (finiteStateWholeVelocity modes state)
    (finite_amplitude_summable modes state) projected.1 output input
  refine ⟨controlled.1, controlled.2.trans ?_⟩
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ majorantNonneg majorant 2) (sq_nonneg _))
    (projected.2.trans (run_receipt_moment_control order index time).2)
    (tsum_nonneg fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem normSq_sub_le (left right : ℂ) :
    Complex.normSq (left - right) ≤ 2 * Complex.normSq left + 2 * Complex.normSq right := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have bound := pow_le_pow_left₀ (norm_nonneg (left - right)) (norm_sub_le left right) 2
  nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

theorem correction_moment_row_le (modes : Finset IntegerWavevector) (order : ℕ)
    (state : ComplexVorticityHilbertState) (output input : Coordinate) (wave : IntegerWavevector) :
    stressMomentDensity order (correctionStress modes state) output input wave ≤
      2 * fluxMomentDensity order (wholeBiotSavartVelocityState state) output input wave +
        2 * fluxMomentDensity order (finiteStateWholeVelocity modes state) output input wave := by
  have projected : Complex.normSq (if wave ∈ modes then
      quadraticFlux (wholeBiotSavartVelocityState state) wave output input else 0) ≤
        Complex.normSq (quadraticFlux (wholeBiotSavartVelocityState state) wave output input) := by
    split_ifs
    · exact le_rfl
    · simpa using Complex.normSq_nonneg (quadraticFlux (wholeBiotSavartVelocityState state) wave output input)
  have sub := normSq_sub_le
    (if wave ∈ modes then quadraticFlux (wholeBiotSavartVelocityState state) wave output input else 0)
    (quadraticFlux (finiteStateWholeVelocity modes state) wave output input)
  have normBound := sub.trans (add_le_add (mul_le_mul_of_nonneg_left projected (by norm_num)) le_rfl)
  have scaled := mul_le_mul_of_nonneg_left normBound (sq_nonneg (frequencySize wave ^ order))
  simp only [stressMomentDensity, correctionStress, projected_velocity_eq, fluxMomentDensity]
  convert! scaled using 1
  ring

theorem run_correction_stress_control (modes : Finset IntegerWavevector) (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (output input : Coordinate) :
    let stress := correctionStress modes ((run stackedShortCurrent index).receipt.wholePath time)
    Summable (stressMomentDensity order stress output input) ∧
      (∑' wave, stressMomentDensity order stress output input wave) ≤ 4 * sourceFluxBudget order index := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have raw := run_receipt_flux_control order index time output input
  have projected := run_projected_flux_control modes order index time output input
  have source := (raw.1.mul_left 2).add (projected.1.mul_left 2)
  have sum := source.of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
    (correction_moment_row_le modes order state output input)
  refine ⟨sum, (sum.tsum_le_tsum (correction_moment_row_le modes order state output input) source).trans ?_⟩
  rw [(raw.1.mul_left 2).tsum_add (projected.1.mul_left 2), tsum_mul_left, tsum_mul_left]
  linarith [raw.2, projected.2]

theorem run_native_correction_control (modes : Finset IntegerWavevector) (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    let state := (run stackedShortCurrent index).receipt.wholePath time
    (Summable fun wave => (frequencySize wave ^ order) ^ 2 *
      complexCoordinateAmplitudeSq (nativeTurbulenceCorrectionAt modes state wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 *
        complexCoordinateAmplitudeSq (nativeTurbulenceCorrectionAt modes state wave)) ≤
          9 * (2 * Real.pi) ^ 4 * (4 * sourceFluxBudget (order + 2) index) := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have actual := constitutive_moment_control (correctionStress modes state) order
    (4 * sourceFluxBudget (order + 2) index)
    (run_correction_stress_control modes (order + 2) index time)
  have read : actionMomentDensity order (correctionStress modes state) = fun wave =>
      (frequencySize wave ^ order) ^ 2 * complexCoordinateAmplitudeSq
        (nativeTurbulenceCorrectionAt modes state wave) := by
    funext wave
    unfold actionMomentDensity
    rw [correctionStress_action modes state
      ((run stackedShortCurrent index).receipt.wholePath_zero_row time) (wholePath_transverse _ time)]
  rw [read] at actual
  exact actual

end
end SaturationMonoid.NavierStokes.NativeFullOrderCorrection
