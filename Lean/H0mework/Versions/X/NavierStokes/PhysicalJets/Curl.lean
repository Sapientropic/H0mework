import H0mework.Versions.X.NavierStokes.SourceAction.Evolution

set_option autoImplicit false
open scoped BigOperators

namespace SaturationMonoid.NavierStokes.NativeFullOrderCurl

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderEvolution

noncomputable section

theorem frequency_norm_sq_le (wave : IntegerWavevector) :
    integerWaveNormSq wave ≤ frequencySize wave ^ 2 := by
  have bound := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin 3))) (fun coordinate _ => abs_nonneg (wave coordinate : ℝ))
  simp only [sq_abs] at bound
  apply bound.trans
  apply pow_le_pow_left₀ (Finset.sum_nonneg fun coordinate _ => abs_nonneg _) _ 2
  change (∑ coordinate, |(wave coordinate : ℝ)|) ≤ 1 + ∑ coordinate, |(wave coordinate : ℝ)|
  linarith

theorem vorticity_moment_row_le (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state)
    (order : ℕ) (wave : IntegerWavevector) :
    (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (state wave) ≤
      (2 * Real.pi) ^ 2 * ((frequencySize wave ^ (order + 1)) ^ 2 *
        complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave)) := by
  by_cases nonzero : wave ≠ 0
  · have identity := biotSavartVelocityCoefficient_normSq_of_transverse wave (state wave)
      nonzero (transverse wave)
    have positive : 0 < (2 * Real.pi) ^ 2 * integerWaveNormSq wave :=
      mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos nonzero)
    have recover := (eq_div_iff positive.ne').mp identity
    rw [← recover]
    have bound := mul_le_mul_of_nonneg_left (frequency_norm_sq_le wave)
      (mul_nonneg (sq_nonneg (frequencySize wave ^ order))
        (mul_nonneg (sq_nonneg (2 * Real.pi))
          (complexCoordinateVectorNormSq_nonneg (finiteStateVelocityCoefficient state wave))))
    simpa only [finiteStateVelocityCoefficient, pow_succ, mul_pow,
      mul_assoc, mul_comm, mul_left_comm] using bound
  · have waveZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [zero, finiteStateVelocityCoefficient, complexCoordinateVectorNormSq]

theorem vorticity_moments_of_velocity (state : ComplexVorticityHilbertState)
    (zero : state 0 = 0) (transverse : WholeStateTransverse state) (order : ℕ)
    (paid : Summable fun wave => (frequencySize wave ^ (order + 1)) ^ 2 *
      complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave)) :
    (Summable fun wave => (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (state wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (state wave)) ≤
        (2 * Real.pi) ^ 2 * (∑' wave, (frequencySize wave ^ (order + 1)) ^ 2 *
          complexCoordinateVectorNormSq (finiteStateVelocityCoefficient state wave)) := by
  have summable := (paid.mul_left ((2 * Real.pi) ^ 2)).of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _))
    (vorticity_moment_row_le state zero transverse order)
  refine ⟨summable, ?_⟩
  rw [← tsum_mul_left]
  exact summable.tsum_le_tsum (vorticity_moment_row_le state zero transverse order)
    (paid.mul_left ((2 * Real.pi) ^ 2))

theorem stacked_vorticity_all_moments (order : ℕ)
    (time : Icc (0 : ℝ) (wholeRestartDuration stackedPhysicalSeed)) :
    (Summable fun wave => (frequencySize wave ^ order) ^ 2 *
      complexCoordinateVectorNormSq (stackedReceipt.wholePath time wave)) ∧
      (∑' wave, (frequencySize wave ^ order) ^ 2 *
        complexCoordinateVectorNormSq (stackedReceipt.wholePath time wave)) ≤
          (2 * Real.pi) ^ 2 * stackedMomentBudget (order + 1) := by
  have velocity := stacked_receipt_all_moments (order + 1) time
  have vorticity := vorticity_moments_of_velocity (stackedReceipt.wholePath time)
    (stackedReceipt.wholePath_zero_row time) (wholePath_transverse stackedReceipt time) order velocity.1
  exact ⟨vorticity.1, vorticity.2.trans (mul_le_mul_of_nonneg_left velocity.2 (sq_nonneg _))⟩

end
end SaturationMonoid.NavierStokes.NativeFullOrderCurl
