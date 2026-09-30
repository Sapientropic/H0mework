import H0mework.Versions.X.NavierStokes.TimeJets.TimeBilinear
import H0mework.Versions.X.NavierStokes.TimeJets.Time

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeHigherTimeJetsSource

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderAction NativeFullOrderNext NativeFullOrderSynthesis NativeFullOrderTime NativeHigherTimeJets NativeFullOrderFlux

noncomputable section

def sourceVelocity (index : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath
    (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual))

def sourceRate (index : ℕ) (actual : ℝ) : ComplexVorticityHilbertState :=
  ∑' wave, lp.single 2 wave (receiptMomentumAction (run stackedShortCurrent index).receipt wave actual)

private theorem norm_le_rowAmplitude (row : ComplexCoordinateVector) : ‖row‖ ≤ rowAmplitude row := by
  apply Real.le_sqrt_of_sq_le
  exact complexCoordinateVector_norm_sq_le_amplitudeSq row

private theorem single_velocity_bound (index : ℕ) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ‖(lp.single 2 wave (receiptVelocityRow (run stackedShortCurrent index).receipt wave time.1) : ComplexVorticityHilbertState)‖ ≤
      Real.sqrt (runMomentBudget 4 index) * decay wave := by
  rw [lp.norm_single (by norm_num), receipt_velocity_row_eq _ wave time]
  apply (norm_le_rowAmplitude _).trans
  simpa only [pow_zero, one_mul, Nat.zero_add] using run_velocity_decay 0 index time wave

private theorem single_rate_bound (index : ℕ) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ‖(lp.single 2 wave (receiptMomentumAction (run stackedShortCurrent index).receipt wave time.1) : ComplexVorticityHilbertState)‖ ≤
      rateBudget 0 index * decay wave := by
  rw [lp.norm_single (by norm_num)]
  apply (norm_le_rowAmplitude _).trans
  simpa only [pow_zero, one_mul] using run_momentum_decay 0 index time wave

theorem sourceRate_summable (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    Summable fun wave => (lp.single 2 wave
      (receiptMomentumAction (run stackedShortCurrent index).receipt wave time.1) : ComplexVorticityHilbertState) :=
  (decay_summable.mul_left (rateBudget 0 index)).of_norm_bounded (fun wave => single_rate_bound index wave time)

theorem sourceRate_row (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (wave : IntegerWavevector) :
    sourceRate index time.1 wave = receiptMomentumAction (run stackedShortCurrent index).receipt wave time.1 := by
  have read := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).map_tsum
    (sourceRate_summable index time)
  change (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave) (sourceRate index time.1) = _
  rw [sourceRate, read]
  change (∑' first, (lp.single 2 first (receiptMomentumAction (run stackedShortCurrent index).receipt first time.1) :
    ComplexVorticityHilbertState) wave) = _
  rw [tsum_eq_single wave]
  · exact lp.single_apply_self 2 _ _
  · intro first different
    exact lp.single_apply_ne 2 _ _ different.symm

theorem sourceVelocity_eq_sum (index : ℕ) :
    sourceVelocity index = fun actual => ∑' wave, (lp.single 2 wave
      (receiptVelocityRow (run stackedShortCurrent index).receipt wave
        (clamp (run stackedShortCurrent index).duration (run stackedShortCurrent index).receipt.requestedTimePos actual)) :
          ComplexVorticityHilbertState) := by
  funext actual
  have generated := (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (sourceVelocity index actual)).tsum_eq
  rw [← generated]
  apply tsum_congr
  intro wave
  congr 1
  exact (receipt_velocity_row_eq _ wave
    (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual)).symm

theorem sourceVelocity_hasDerivWithinAt (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    HasDerivWithinAt (sourceVelocity index) (sourceRate index time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  let receipt := (run stackedShortCurrent index).receipt
  have actual := hasDerivWithinAt_tsum_Icc _ receipt.requestedTimePos
    (fun wave sample => (lp.single 2 wave (receiptVelocityRow receipt wave sample) : ComplexVorticityHilbertState))
    (fun wave sample => (lp.single 2 wave (receiptMomentumAction receipt wave sample) : ComplexVorticityHilbertState))
    (fun wave => Real.sqrt (runMomentBudget 4 index) * decay wave)
    (fun wave => rateBudget 0 index * decay wave)
    (decay_summable.mul_left _) (decay_summable.mul_left _)
    (fun wave sample inside => (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt sample
      (receipt_velocity_row_hasDerivAt receipt wave ⟨sample, inside⟩))
    (fun wave => ((lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp
      (receiptMomentumAction_continuous receipt wave)).continuousOn)
    (fun wave sample inside => single_velocity_bound index wave ⟨sample, inside⟩)
    (fun wave sample inside => single_rate_bound index wave ⟨sample, inside⟩) time
  rw [sourceVelocity_eq_sum]
  exact actual

theorem sourceVelocity_on_interval (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    sourceVelocity index time.1 = wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time) := by
  unfold sourceVelocity
  rw [projIcc_of_mem (run stackedShortCurrent index).receipt.requestedTimePos.le time.2]

private theorem decay_le_one (wave : IntegerWavevector) : decay wave ≤ 1 := by
  have size : 1 ≤ frequencySize wave := by
    unfold frequencySize
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have square : 1 ≤ frequencySize wave ^ 2 := one_le_pow₀ size
  have inverted : (frequencySize wave ^ 2)⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) square
  have actual := pow_le_pow_left₀ (inv_nonneg.mpr (sq_nonneg (frequencySize wave))) inverted 2
  simp only [one_pow] at actual
  convert! actual using 1

theorem sourceRate_moment_control (index order : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    Summable (velocityMomentDensity order (sourceRate index time.1)) ∧
      (∑' wave, velocityMomentDensity order (sourceRate index time.1) wave) ≤
        rateBudget order index ^ 2 * ∑' wave, decay wave := by
  have point (wave) : velocityMomentDensity order (sourceRate index time.1) wave ≤
      rateBudget order index ^ 2 * decay wave := by
    have source := run_momentum_decay order index time wave
    have squared := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (frequencySize_pos wave).le _) (rowAmplitude_nonneg _)) source 2
    rw [mul_pow, mul_pow, rowAmplitude_sq] at squared
    have decayNonnegative : 0 ≤ decay wave := sq_nonneg _
    have decaySquare : decay wave ^ 2 ≤ decay wave := by nlinarith [decay_le_one wave]
    change (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (sourceRate index time.1 wave) ≤ _
    rw [sourceRate_row, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    exact squared.trans (mul_le_mul_of_nonneg_left decaySquare (sq_nonneg _))
  have generated := (decay_summable.mul_left (rateBudget order index ^ 2)).of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) point
  refine ⟨generated, ?_⟩
  have bound := generated.tsum_le_tsum point (decay_summable.mul_left (rateBudget order index ^ 2))
  simpa only [tsum_mul_left] using bound

theorem source_quadraticFlux_hasDerivWithinAt (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (wave : IntegerWavevector) (output input : Coordinate) :
    HasDerivWithinAt (fun actual => quadraticFlux (sourceVelocity index actual) wave output input)
      (mixedFlux (sourceRate index time.1) (sourceVelocity index time.1) wave output input +
        mixedFlux (sourceVelocity index time.1) (sourceRate index time.1) wave output input)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 :=
  mixedFlux_hasDerivWithinAt (sourceVelocity_hasDerivWithinAt index time)
    (sourceVelocity_hasDerivWithinAt index time) wave output input

end
end SaturationMonoid.NavierStokes.NativeHigherTimeJetsSource
