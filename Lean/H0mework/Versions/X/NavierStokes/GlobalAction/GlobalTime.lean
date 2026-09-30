import H0mework.Versions.X.NavierStokes.GlobalAction.Global
import H0mework.Versions.X.NavierStokes.TimeJets.TimeSource

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeOldGlobalTime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativeFullOrderAction NativeFullOrderTime NativeOldGlobalMoments NativePhysicalFourier

noncomputable section

def velocity (trajectory : OriginalGlobal) (time : ℝ) : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState (trajectory.physicalPath time)

def rateRow (trajectory : OriginalGlobal) (time : ℝ) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  biotSavartVelocityCoefficient wave
    (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff (trajectory.physicalPath time) wave)

def rate (trajectory : OriginalGlobal) (time : ℝ) : ComplexVorticityHilbertState :=
  ∑' wave, lp.single 2 wave (rateRow trajectory time wave)

def windowRateBudget (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (windowIndex trajectory horizon + 1), rateBudget order index

theorem receipt_momentum_at {nu : Viscosity} {initial : ComplexVorticityHilbertState} {horizon : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial horizon) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) horizon) :
    receiptMomentumAction receipt wave time.1 =
      biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt nu.coeff (receipt.wholePath time) wave) := by
  change biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt nu.coeff
    (receipt.wholePath (projIcc (0 : ℝ) horizon receipt.requestedTimePos.le time.1)) wave) = _
  rw [projIcc_of_mem receipt.requestedTimePos.le time.2]

theorem velocity_decay (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ)
    (time : Icc (0 : ℝ) horizon) (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (velocity trajectory time.1 wave) ≤
      Real.sqrt (windowMomentBudget trajectory horizon (order + 4)) * decay wave := by
  have source := global_window_moment_control trajectory horizon (order + 4) time
  apply weighted_row_decay _ order _ _ _ wave
  · have paid := source.1
    unfold momentDensity at paid
    simpa only [velocity, wholeBiotSavartVelocityState_apply,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  · simpa only [velocity, moment, momentDensity, wholeBiotSavartVelocityState_apply,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using source.2

theorem rate_decay (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ)
    (time : Icc (0 : ℝ) horizon) (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (rateRow trajectory time.1 wave) ≤
      windowRateBudget trajectory horizon order * decay wave := by
  obtain ⟨index, inside, localTime, same⟩ := window_reads_original_receipt trajectory horizon time
  have exactAction : rateRow trajectory time.1 wave =
      receiptMomentumAction (run stackedShortCurrent index).receipt wave localTime.1 := by
    rw [receipt_momentum_at]
    simp only [rateRow, same]
  rw [exactAction]
  apply (run_momentum_decay order index localTime wave).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.single_le_sum _ (Finset.mem_range.mpr inside)
  intro actual _
  unfold rateBudget
  exact add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg butterflyGainViscosity.coeff_pos.le (sq_nonneg _)) (Real.sqrt_nonneg _))

theorem observe_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (trajectory : OriginalGlobal) (order : ℕ) (factor : ℝ) (factorNonnegative : 0 ≤ factor)
    (observe : IntegerWavevector → ComplexCoordinateVector →L[ℝ] E)
    (bounded : ∀ wave row, ‖observe wave row‖ ≤ factor * (frequencySize wave ^ order * rowAmplitude row))
    (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivWithinAt (fun actual => ∑' wave, observe wave (velocity trajectory actual wave))
      (∑' wave, observe wave (rateRow trajectory time wave)) (Ici (0 : ℝ)) time := by
  let horizon := time + 1
  have positive : 0 < horizon := by dsimp [horizon]; linarith
  let receipt := (WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive
  have point : time ∈ Icc (0 : ℝ) horizon := ⟨nonnegative, by dsimp [horizon]; linarith⟩
  have velocityEq (actual : Icc (0 : ℝ) horizon) (wave : IntegerWavevector) :
      receiptVelocityRow receipt wave actual.1 = velocity trajectory actual.1 wave := by
    rw [receipt_velocity_row_eq, WholeGlobalReceipt.ofTrajectory_path]
    rfl
  have rateEq (actual : Icc (0 : ℝ) horizon) (wave : IntegerWavevector) :
      receiptMomentumAction receipt wave actual.1 = rateRow trajectory actual.1 wave := by
    rw [receipt_momentum_at, WholeGlobalReceipt.ofTrajectory_path]
    rfl
  have observed := hasDerivWithinAt_tsum_Icc horizon positive
    (fun wave actual => observe wave (receiptVelocityRow receipt wave actual))
    (fun wave actual => observe wave (receiptMomentumAction receipt wave actual))
    (fun wave => (factor * Real.sqrt (windowMomentBudget trajectory horizon (order + 4))) * decay wave)
    (fun wave => (factor * windowRateBudget trajectory horizon order) * decay wave)
    (decay_summable.mul_left _) (decay_summable.mul_left _)
    (fun wave actual inside => (observe wave).hasFDerivAt.comp_hasDerivAt actual
      (receipt_velocity_row_hasDerivAt receipt wave ⟨actual, inside⟩))
    (fun wave => ((observe wave).continuous.comp (receiptMomentumAction_continuous receipt wave)).continuousOn)
    (fun wave actual inside => by
      rw [velocityEq ⟨actual, inside⟩ wave]
      exact (bounded wave _).trans (by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left (velocity_decay trajectory horizon order ⟨actual, inside⟩ wave) factorNonnegative)))
    (fun wave actual inside => by
      rw [rateEq ⟨actual, inside⟩ wave]
      exact (bounded wave _).trans (by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left (rate_decay trajectory horizon order ⟨actual, inside⟩ wave) factorNonnegative)))
    ⟨time, point⟩
  have inputEq (actual : ℝ) (inside : actual ∈ Icc (0 : ℝ) horizon) :
      (∑' wave, observe wave (velocity trajectory actual wave)) =
        ∑' wave, observe wave (receiptVelocityRow receipt wave (clamp horizon positive actual)) := by
    rw [clamp_of_mem positive inside]
    exact tsum_congr fun wave => congrArg (observe wave) (velocityEq ⟨actual, inside⟩ wave).symm
  have outputEq : (∑' wave, observe wave (receiptMomentumAction receipt wave time)) =
      ∑' wave, observe wave (rateRow trajectory time wave) :=
    tsum_congr fun wave => congrArg (observe wave) (rateEq ⟨time, point⟩ wave)
  rw [outputEq] at observed
  apply (observed.congr_of_mem inputEq point).mono_of_mem_nhdsWithin
  have before : Iio horizon ∈ 𝓝 time := Iio_mem_nhds (by dsimp [horizon]; linarith)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds before] with actual nonneg earlier
  exact ⟨nonneg, earlier.le⟩

private theorem norm_le_rowAmplitude (row : ComplexCoordinateVector) : ‖row‖ ≤ rowAmplitude row :=
  Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq row)

theorem velocity_hasDerivWithinAt (trajectory : OriginalGlobal) (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivWithinAt (velocity trajectory) (rate trajectory time) (Ici (0 : ℝ)) time := by
  have source := observe_hasDerivWithinAt trajectory 0 1 zero_le_one
    (fun wave => lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave)
    (fun wave row => by
      change ‖(lp.single 2 wave row : ComplexVorticityHilbertState)‖ ≤ 1 * (frequencySize wave ^ 0 * rowAmplitude row)
      rw [lp.norm_single (by norm_num), pow_zero, one_mul, one_mul]
      exact norm_le_rowAmplitude row) time nonnegative
  exact source.congr_of_mem (fun actual _ =>
    (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (velocity trajectory actual)).tsum_eq.symm) nonnegative

theorem velocity_hasDerivAt (trajectory : OriginalGlobal) (time : ℝ) (positive : 0 < time) :
    HasDerivAt (velocity trajectory) (rate trajectory time) time :=
  (velocity_hasDerivWithinAt trajectory time positive.le).hasDerivAt (Ici_mem_nhds positive)

theorem rate_summable (trajectory : OriginalGlobal) (time : ℝ) (nonnegative : 0 ≤ time) :
    Summable fun wave => (lp.single 2 wave (rateRow trajectory time wave) : ComplexVorticityHilbertState) := by
  apply (decay_summable.mul_left (windowRateBudget trajectory (time + 1) 0)).of_norm_bounded
  intro wave
  rw [lp.norm_single (by norm_num)]
  apply (norm_le_rowAmplitude _).trans
  simpa only [pow_zero, one_mul] using rate_decay trajectory (time + 1) 0
    ⟨time, nonnegative, by linarith⟩ wave

theorem rate_apply (trajectory : OriginalGlobal) (time : ℝ) (nonnegative : 0 ≤ time) (wave : IntegerWavevector) :
    rate trajectory time wave = rateRow trajectory time wave := by
  have read := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).map_tsum
    (rate_summable trajectory time nonnegative)
  change (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave) (rate trajectory time) = _
  rw [rate, read]
  change (∑' first, (lp.single 2 first (rateRow trajectory time first) : ComplexVorticityHilbertState) wave) = _
  rw [tsum_eq_single wave]
  · exact lp.single_apply_self 2 _ _
  · intro first different
    exact lp.single_apply_ne 2 _ _ different.symm

def windowRateMomentBudget (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ) : ℝ :=
  (∑ index ∈ Finset.range (windowIndex trajectory horizon + 1), rateBudget order index ^ 2) * ∑' wave, decay wave

theorem rate_moment_control (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ)
    (time : Icc (0 : ℝ) horizon) :
    Summable (velocityMomentDensity order (rate trajectory time.1)) ∧
      (∑' wave, velocityMomentDensity order (rate trajectory time.1) wave) ≤
        windowRateMomentBudget trajectory horizon order := by
  obtain ⟨index, inside, localTime, same⟩ := window_reads_original_receipt trajectory horizon time
  have sourceEq : rate trajectory time.1 = NativeHigherTimeJetsSource.sourceRate index localTime.1 := by
    apply lp.ext
    funext wave
    rw [rate_apply trajectory time.1 time.2.1 wave, NativeHigherTimeJetsSource.sourceRate_row index localTime wave,
      receipt_momentum_at]
    simp only [rateRow, same]
  rw [sourceEq]
  have source := NativeHigherTimeJetsSource.sourceRate_moment_control index order localTime
  refine ⟨source.1, source.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun actual _ => sq_nonneg (rateBudget order actual)) (Finset.mem_range.mpr inside))
    (tsum_nonneg fun _ => sq_nonneg _)

def globalSpatialWord (trajectory : OriginalGlobal) (order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : ℝ) : PhysicalSpace :=
  iteratedFDeriv ℝ order (spatialField (velocity trajectory time)) point directions

def globalWordRate (trajectory : OriginalGlobal) (order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : ℝ) : PhysicalSpace :=
  ∑' wave, observeWord order directions wave point (rateRow trajectory time wave)

theorem globalSpatialWord_eq_sum (trajectory : OriginalGlobal) (order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : ℝ) (nonnegative : 0 ≤ time) :
    globalSpatialWord trajectory order directions point time =
      ∑' wave, observeWord order directions wave point (velocity trajectory time wave) := by
  have regular := global_window_momentRegular trajectory (time + 1) ⟨time, nonnegative, by linarith⟩
  have moments (order : ℕ) : Summable fun wave => frequencySize wave ^ order * amplitude (velocity trajectory time) wave := by
    apply summable_moment_of_square
    rw [velocity, source_square_moment_eq]
    exact regular (order + 2)
  rw [globalSpatialWord, spatialField_word_eq _ moments]
  exact tsum_congr fun _ => rfl

theorem globalSpatialWord_hasDerivWithinAt (trajectory : OriginalGlobal) (order : ℕ)
    (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivWithinAt (globalSpatialWord trajectory order directions point)
      (globalWordRate trajectory order directions point time) (Ici (0 : ℝ)) time := by
  have source := observe_hasDerivWithinAt trajectory order (wordNorm order directions) (wordNorm_nonneg order directions)
    (fun wave => observeWord order directions wave point) (fun wave row => observeWord_norm_le order directions wave point row)
    time nonnegative
  exact source.congr_of_mem (fun actual inside => globalSpatialWord_eq_sum trajectory order directions point actual inside) nonnegative

theorem globalSpatialWord_hasDerivAt (trajectory : OriginalGlobal) (order : ℕ)
    (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (time : ℝ) (positive : 0 < time) :
    HasDerivAt (globalSpatialWord trajectory order directions point)
      (globalWordRate trajectory order directions point time) time :=
  (globalSpatialWord_hasDerivWithinAt trajectory order directions point time positive.le).hasDerivAt (Ici_mem_nhds positive)

theorem globalWordRate_bound (trajectory : OriginalGlobal) (horizon : ℝ) (order : ℕ)
    (directions : Fin order → PhysicalSpace) (point : PhysicalSpace) (time : Icc (0 : ℝ) horizon) :
    Summable (fun wave => observeWord order directions wave point (rateRow trajectory time.1 wave)) ∧
      ‖globalWordRate trajectory order directions point time.1‖ ≤
        (wordNorm order directions * windowRateBudget trajectory horizon order) * ∑' wave, decay wave := by
  have bound (wave) : ‖observeWord order directions wave point (rateRow trajectory time.1 wave)‖ ≤
      (wordNorm order directions * windowRateBudget trajectory horizon order) * decay wave :=
    (observeWord_norm_le order directions wave point _).trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (rate_decay trajectory horizon order time wave) (wordNorm_nonneg order directions))
  have majorant := decay_summable.mul_left (wordNorm order directions * windowRateBudget trajectory horizon order)
  have normPaid := majorant.of_nonneg_of_le (fun _ => norm_nonneg _) bound
  refine ⟨normPaid.of_norm, (norm_tsum_le_tsum_norm normPaid).trans ?_⟩
  simpa only [tsum_mul_left] using normPaid.tsum_le_tsum bound majorant

end
end SaturationMonoid.NavierStokes.NativeOldGlobalTime
