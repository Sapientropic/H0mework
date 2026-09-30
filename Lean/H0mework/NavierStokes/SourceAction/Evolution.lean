import H0mework.NavierStokes.SourceAction.Convolution
import H0mework.NavierStokes.SourceAction.Energy
import H0mework.NavierStokes.StressAction.Stress
import H0mework.NavierStokes.SourceAction.Limit
import H0mework.NavierStokes.SourceAction.Initial

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativeFullOrderEvolution

open Set Filter MeasureTheory
open NativeFullOrderAction NativeFullOrderEnergy NativeStressSource
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalTimeConsumer
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalGronwall
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall

noncomputable section

theorem finite_amplitude_summable (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    Summable (amplitude (finiteStateWholeVelocity modes state)) := by
  apply summable_of_ne_finset_zero (s := modes)
  intro wave outside
  simp [amplitude, vorticityRowAmplitude, finiteStateWholeVelocity_apply, outside,
    complexCoordinateAmplitudeSq]

theorem finite_majorant_eq (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    (∑' wave, amplitude (finiteStateWholeVelocity modes state) wave) =
      finiteStateVelocityMajorant modes state := by
  rw [tsum_eq_sum (s := modes)]
  · apply Finset.sum_congr rfl
    intro wave inside
    simp only [amplitude, vorticityRowAmplitude, finiteStateWholeVelocity_apply, if_pos inside]
  · intro wave outside
    simp [amplitude, vorticityRowAmplitude, finiteStateWholeVelocity_apply, outside,
      complexCoordinateAmplitudeSq]

theorem finite_weighted_amplitude_norm_sq (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    ‖weighted order ceiling nonnegative (amplitude (finiteStateWholeVelocity modes state))‖ ^ 2 =
      weightedVelocityEnergy modes (wordWeight order ceiling) state := by
  have normEq := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (weighted order ceiling nonnegative (amplitude (finiteStateWholeVelocity modes state)))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at normEq
  rw [normEq, tsum_eq_sum (s := modes)]
  · apply Finset.sum_congr rfl
    intro wave inside
    rw [weighted_apply, Real.norm_eq_abs, sq_abs, mul_pow]
    change _ * vorticityRowAmplitude (finiteStateWholeVelocity modes state) wave ^ 2 = _
    rw [vorticityRowAmplitude_sq, finiteStateWholeVelocity_apply, if_pos inside]
  · intro wave outside
    simp [weighted_apply, amplitude, vorticityRowAmplitude, finiteStateWholeVelocity_apply,
      outside, complexCoordinateAmplitudeSq]

theorem finite_work_eq_stress (modes : Finset IntegerWavevector)
    (weight : IntegerWavevector → ℝ) (state : ComplexVorticityHilbertState) :
    weightedVelocityNonlinearWork modes weight state =
      ∑ wave ∈ modes, weight wave ^ 2 * complexCoordinateRealInner
        (finiteStateWholeVelocity modes state wave)
        (nativeFluidStressDivergenceCoefficient (quadraticFlux (finiteStateWholeVelocity modes state)) wave) := by
  apply Finset.sum_congr rfl
  intro wave inside
  rw [finiteStateWholeVelocity_apply, if_pos inside,
    quadraticFlux_divergence _ (finiteStateWholeVelocity_transverse modes state)]

theorem finite_velocity_supported (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) (outside : wave ∉ modes) :
    finiteStateWholeVelocity modes state wave = 0 := by
  simp only [finiteStateWholeVelocity_apply, if_neg outside]

theorem finite_energy_eq (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (state : ComplexVorticityHilbertState) :
    NativeFullOrderStress.energy modes order ceiling (finiteStateWholeVelocity modes state) =
      weightedVelocityEnergy modes (wordWeight order ceiling) state := by
  apply Finset.sum_congr rfl
  intro wave inside
  rw [finiteStateWholeVelocity_apply, if_pos inside, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

theorem finite_dissipation_eq (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (state : ComplexVorticityHilbertState) :
    NativeFullOrderStress.dissipation modes order ceiling (finiteStateWholeVelocity modes state) =
      weightedVelocityDissipation modes (wordWeight order ceiling) state := by
  apply Finset.sum_congr rfl
  intro wave inside
  rw [finiteStateWholeVelocity_apply, if_pos inside, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]

def wordRate (order : ℕ) (nu : Viscosity) : ℝ := (6 * 2 ^ order) ^ 2 / nu.coeff

theorem wordRate_nonneg (order : ℕ) (nu : Viscosity) : 0 ≤ wordRate order nu :=
  div_nonneg (sq_nonneg _) nu.coeff_pos.le

theorem finite_action_bound (modes : Finset IntegerWavevector) (order : ℕ) (ceiling : ℝ)
    (nonnegative : 0 ≤ ceiling) (state : ComplexVorticityHilbertState) (nu : Viscosity) :
    2 * weightedVelocityNonlinearWork modes (wordWeight order ceiling) state -
      2 * nu.coeff * weightedVelocityDissipation modes (wordWeight order ceiling) state ≤
        wordRate order nu * finiteStateVelocityMajorant modes state ^ 2 *
          weightedVelocityEnergy modes (wordWeight order ceiling) state := by
  have action := NativeFullOrderStress.power_absorbed modes order ceiling nonnegative
    (finiteStateWholeVelocity modes state) (finite_amplitude_summable modes state)
    (finite_velocity_supported modes state) nu.coeff nu.coeff_pos
  rw [finite_majorant_eq, finite_energy_eq, finite_dissipation_eq] at action
  rw [finite_work_eq_stress]
  exact action

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed] {seed : Seed} {radius : ℕ}

theorem stage_energy_exp (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time) ≤
      weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory 0) *
        Real.exp (wordRate order nu * ∫ actual in 0..time,
          finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory actual) ^ 2) := by
  have coefficientContinuous : ContinuousOn (fun actual => wordRate order nu *
      finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory actual) ^ 2)
      (Icc 0 (wholeRestartDuration seed)) := by
    intro actual actualInside
    exact ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
      (wholeRestartModes radius) stage.trajectory actual _ (stage.physical actual actualInside).1).pow 2
        |>.const_mul (wordRate order nu)).continuousWithinAt
  have bound := le_initial_mul_exp_integral_of_hasDerivAt_le_mul
    (fun actual actualInside => stage_weightedVelocityEnergy_action_hasDerivAt stage
      (wordWeight order ceiling) actual actualInside) coefficientContinuous
    (fun actual _ => finite_action_bound (wholeRestartModes radius) order ceiling nonnegative
      (stage.trajectory actual) nu) time inside
  rw [intervalIntegral.integral_const_mul] at bound
  exact bound

theorem stage_majorant_integral_le (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    (∫ actual in 0..time,
      finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory actual) ^ 2) ≤
        wholeRestartVelocityCeiling seed := by
  have continuous : ContinuousOn (fun actual =>
      finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory actual) ^ 2)
      (Icc 0 (wholeRestartDuration seed)) := by
    intro actual actualInside
    exact ((finiteStateVelocityMajorant_continuousAt_of_hasDerivAt
      (wholeRestartModes radius) stage.trajectory actual _ (stage.physical actual actualInside).1).pow 2).continuousWithinAt
  have integrable : IntervalIntegrable (fun actual =>
      finiteStateVelocityMajorant (wholeRestartModes radius) (stage.trajectory actual) ^ 2)
      volume 0 (wholeRestartDuration seed) :=
    ContinuousOn.intervalIntegrable_of_Icc (wholeRestartDuration_pos seed).le continuous
  exact (intervalIntegral.integral_mono_interval le_rfl inside.1 inside.2
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) integrable).trans stage.uniformScalarBudget.2.2.1

theorem stage_energy_source_bound (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (order : ℕ) (ceiling : ℝ) (nonnegative : 0 ≤ ceiling)
    (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory time) ≤
      weightedVelocityEnergy (wholeRestartModes radius) (wordWeight order ceiling) (stage.trajectory 0) *
        Real.exp (wordRate order nu * wholeRestartVelocityCeiling seed) := by
  apply (stage_energy_exp stage order ceiling nonnegative time inside).trans
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (stage_majorant_integral_le stage time inside)
      (wordRate_nonneg order nu)))
  rw [← weightedVelocityRead_norm_sq]
  exact sq_nonneg _

def frequencyCeiling (modes : Finset IntegerWavevector) : ℝ := ∑ wave ∈ modes, frequencySize wave

theorem frequencyCeiling_nonneg (modes : Finset IntegerWavevector) : 0 ≤ frequencyCeiling modes :=
  Finset.sum_nonneg fun wave _ => frequencySize_nonneg wave

theorem wordWeight_full_on_modes (modes : Finset IntegerWavevector) (order : ℕ)
    (wave : IntegerWavevector) (inside : wave ∈ modes) :
    wordWeight order (frequencyCeiling modes) wave = frequencySize wave ^ order := by
  unfold wordWeight frequencyCeiling
  rw [min_eq_left (Finset.single_le_sum (fun actual _ => frequencySize_nonneg actual) inside)]

theorem energy_full_on_modes (modes : Finset IntegerWavevector) (order : ℕ)
    (state : ComplexVorticityHilbertState) :
    weightedVelocityEnergy modes (wordWeight order (frequencyCeiling modes)) state =
      weightedVelocityEnergy modes (fun wave => frequencySize wave ^ order) state := by
  apply Finset.sum_congr rfl
  intro wave inside
  rw [wordWeight_full_on_modes modes order wave inside]

theorem stage_full_energy_source_bound (stage : GeneratedWholeRestartCanonicalStage seed radius)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc 0 (wholeRestartDuration seed)) :
    weightedVelocityEnergy (wholeRestartModes radius) (fun wave => frequencySize wave ^ order) (stage.trajectory time) ≤
      weightedVelocityEnergy (wholeRestartModes radius) (fun wave => frequencySize wave ^ order) (stage.trajectory 0) *
        Real.exp (wordRate order nu * wholeRestartVelocityCeiling seed) := by
  have source := stage_energy_source_bound stage order (frequencyCeiling (wholeRestartModes radius))
    (frequencyCeiling_nonneg _) time inside
  simpa only [energy_full_on_modes] using source

theorem generated_receipt_full_energy_bound
    (replay : GeneratedWholeRestartCanonicalReplay seed) (order : ℕ) (initialBudget : ℝ)
    (initialPaid : ∀ radius, weightedVelocityEnergy (wholeRestartModes radius)
      (fun wave => frequencySize wave ^ order) ((replay.current radius).trajectory 0) ≤ initialBudget)
    (time : Icc (0 : ℝ) (wholeRestartDuration seed)) :
    Summable (fun wave => (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient
        ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
        (finiteStateVelocityCoefficient
          ((generatedWholeRestartWholeContinuousMildSerrinReceipt replay).wholePath time) wave)) ≤
        initialBudget * Real.exp (wordRate order nu * wholeRestartVelocityCeiling seed) := by
  refine NativeFullOrderLimit.generated_receipt_weightedVelocity_summable_and_tsum_le
    replay (fun wave => frequencySize wave ^ order)
    (initialBudget * Real.exp (wordRate order nu * wholeRestartVelocityCeiling seed)) ?_ time
  intro radius actual inside
  exact (stage_full_energy_source_bound (replay.current radius) order actual inside).trans
    (mul_le_mul_of_nonneg_right (initialPaid radius) (Real.exp_pos _).le)

open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderInitial

def stackedMomentBudget (order : ℕ) : ℝ :=
  initialMomentBudget order * Real.exp (wordRate order butterflyGainViscosity *
    wholeRestartVelocityCeiling stackedPhysicalSeed)

theorem stacked_receipt_all_moments (order : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration stackedPhysicalSeed)) :
    Summable (fun wave => (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient (stackedReceipt.wholePath time) wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
        (finiteStateVelocityCoefficient (stackedReceipt.wholePath time) wave)) ≤ stackedMomentBudget order := by
  refine generated_receipt_full_energy_bound stackedReplay order (initialMomentBudget order) ?_ time
  intro radius
  have initial := stacked_replay_initial_capped_energy_le order
    (frequencyCeiling (wholeRestartModes radius)) (frequencyCeiling_nonneg _) radius
  simpa only [energy_full_on_modes] using initial

theorem stacked_short_receipt_all_moments (order : ℕ) (time : Icc (0 : ℝ) stackedShortDuration) :
    Summable (fun wave => (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient (stackedShortReceipt.wholePath time) wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
        (finiteStateVelocityCoefficient (stackedShortReceipt.wholePath time) wave)) ≤ stackedMomentBudget order :=
  stacked_receipt_all_moments order
    ⟨time.1, time.2.1, time.2.2.trans stackedShortDuration_le_full⟩

theorem stacked_contact_all_moments (order : ℕ) :
    Summable (fun wave => (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
      (finiteStateVelocityCoefficient stackedShortContact.physicalState wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq
        (finiteStateVelocityCoefficient stackedShortContact.physicalState wave)) ≤ stackedMomentBudget order :=
  stacked_short_receipt_all_moments order stackedShortContact.time

end
end SaturationMonoid.NavierStokes.NativeFullOrderEvolution
