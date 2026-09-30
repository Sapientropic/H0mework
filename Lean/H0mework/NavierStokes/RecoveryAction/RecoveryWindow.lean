import H0mework.NavierStokes.RecoveryAction.Recovery
import H0mework.NavierStokes.RecoveryAction.RecoveryRowAction
import H0mework.NavierStokes.TimeJets.TimeRecursion

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryStrongWindow

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis NativeFullOrderTime
open NativeRecoveryControlProducer
open NativeRecoveryRowAction
open NativeTimeJetCarrier NativeStressSource

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

structure ControlledWindow (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (lower upper : ℝ) where
  first : ℝ
  last : ℝ
  lower_lt : lower < first
  ordered : first < last
  upper_lt : last < upper
  first_pos : 0 < first
  last_lt_one : last < 1
  budget : ℕ → ℝ
  paid : ∀ order time, time ∈ Icc first last → Summable (velocityMomentDensity order (velocity receipt time))
  bound : ∀ order time, time ∈ Icc first last →
    (∑' wave, velocityMomentDensity order (velocity receipt time) wave) ≤ budget order

def generatedWindow (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (lower upper : ℝ) (lowerNonnegative : 0 ≤ lower) (ordered : lower < upper) (upperLe : upper ≤ 1) :
    ControlledWindow receipt lower upper := Classical.choice (by
  obtain ⟨first, last, afterLower, orderedTime, beforeUpper, source⟩ :=
    wholeMild_controlled_subinterval ledger receipt lower upper lowerNonnegative ordered upperLe
  let budget (order : ℕ) := Classical.choose (source order)
  have controlled (order : ℕ) := Classical.choose_spec (source order)
  refine ⟨{ first := first
            last := last
            lower_lt := afterLower
            ordered := orderedTime
            upper_lt := beforeUpper
            first_pos := lowerNonnegative.trans_lt afterLower
            last_lt_one := beforeUpper.trans_le upperLe
            budget := budget
            paid := ?_
            bound := ?_ }⟩
  · intro order time inside
    let original : Icc (0 : ℝ) 1 := ⟨time, by constructor <;> linarith [inside.1, inside.2]⟩
    rw [velocity_on_interval receipt original]
    exact (controlled order original inside.1 inside.2).1
  · intro order time inside
    let original : Icc (0 : ℝ) 1 := ⟨time, by constructor <;> linarith [inside.1, inside.2]⟩
    rw [velocity_on_interval receipt original]
    exact (controlled order original inside.1 inside.2).2)

variable {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {lower upper : ℝ}

theorem ControlledWindow.velocity_decay (window : ControlledWindow receipt lower upper)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc window.first window.last) (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (velocity receipt time wave) ≤
      Real.sqrt (window.budget (order + 4)) * decay wave := by
  apply weighted_row_decay _ order _ _ _ wave
  · have paid := window.paid (order + 4) time inside
    unfold velocityMomentDensity at paid
    simpa only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  · simpa only [velocityMomentDensity, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      window.bound (order + 4) time inside

theorem velocity_row_continuous (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (wave : IntegerWavevector) : Continuous (fun actual => velocity receipt actual wave) :=
  (receipt.coordinate_continuous wave).comp continuous_projIcc

theorem ControlledWindow.velocity_continuous (window : ControlledWindow receipt lower upper) :
    ContinuousOn (velocity receipt) (Icc window.first window.last) := by
  have source : ContinuousOn (fun actual => ∑' wave,
      (lp.single 2 wave (velocity receipt actual wave) : ComplexVorticityHilbertState))
      (Icc window.first window.last) := by
    apply continuousOn_tsum
    · intro wave
      exact ((lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp
        (velocity_row_continuous receipt wave)).continuousOn
    · exact decay_summable.mul_left (Real.sqrt (window.budget 4))
    · intro wave time inside
      rw [lp.norm_single (by norm_num)]
      apply (Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq _)).trans
      have paid := window.velocity_decay 0 time inside wave
      simp only [pow_zero, one_mul, Nat.zero_add] at paid
      convert! paid using 1
  exact source.congr (fun time _ =>
    (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (velocity receipt time)).tsum_eq.symm)

theorem ControlledWindow.square_moments (window : ControlledWindow receipt lower upper)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    Summable (fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (velocity receipt time wave)) ∧
      (∑' wave, frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (velocity receipt time wave)) ≤ window.budget order := by
  have paid := window.paid order time inside
  have bound := window.bound order time inside
  unfold velocityMomentDensity at paid bound
  simpa only [← pow_mul, Nat.mul_comm order 2, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using And.intro paid bound

def ControlledWindow.spatialBudget (window : ControlledWindow receipt lower upper) (order : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ((window.budget (order + 2) + ∑' wave, decay wave) / 2)

theorem ControlledWindow.spatial_control (window : ControlledWindow receipt lower upper)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (spatialField (velocity receipt time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (spatialField (velocity receipt time)) point‖ ≤ window.spatialBudget order := by
  have moments (order : ℕ) := (window.square_moments order time inside).1
  refine ⟨spatialField_smooth_of_square _ moments, ?_⟩
  intro order point
  apply (spatialField_bound_of_square _ moments order point).trans
  unfold ControlledWindow.spatialBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact add_le_add (window.square_moments (order + 2) time inside).2 le_rfl

theorem ControlledWindow.row_hasDerivWithinAt (window : ControlledWindow receipt lower upper)
    (wave : IntegerWavevector) (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    HasDerivWithinAt (fun actual => velocity receipt actual wave) (rateRow receipt wave time)
      (Icc window.first window.last) time := by
  by_cases nonzero : wave ≠ 0
  · have subset : Icc window.first window.last ⊆ Icc (0 : ℝ) 1 :=
      Icc_subset_Icc window.first_pos.le window.last_lt_one.le
    have pathAC : AbsolutelyContinuousOnInterval (rowExtension receipt wave) window.first window.last :=
      (rowExtension_absolutelyContinuous receipt wave).mono (by
      simpa only [uIcc_of_le window.ordered.le, uIcc_of_le zero_le_one] using subset)
    have derivative : ∀ᵐ actual : ℝ, actual ∈ Icc window.first window.last →
        HasDerivAt (rowExtension receipt wave) (rateRow receipt wave actual) actual := by
      filter_upwards [rowExtension_derivative_ae receipt wave nonzero] with actual source member
      exact source (subset member)
    have actual := hasDerivWithinAt_of_source_integral (rowExtension receipt wave) (rateRow receipt wave)
      window.first window.last window.ordered.le pathAC
      (rateRow_continuousOn receipt _ window.velocity_continuous wave) derivative time inside
    exact actual.congr_of_mem (fun sample member =>
      (rowExtension_on_interval receipt wave nonzero ⟨sample, subset member⟩).symm) inside
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    have valueZero : (fun actual => velocity receipt actual 0) = fun _ => (0 : ComplexCoordinateVector) := by
      funext actual
      unfold velocity
      rw [receipt.wholePath_apply]
      simp [velocityEndpointWholeMildState_apply, velocityEndpointWholeMildCoefficient]
    have rateZero : rateRow receipt 0 time = 0 := by
      simp [rateRow, nonlinearRow, projectedDivergenceCLM_apply, transverseProjection, integerWaveViscousMultiplier]
    rw [valueZero, rateZero]
    exact hasDerivWithinAt_const time _ _

def ControlledWindow.majorantBudget (window : ControlledWindow receipt lower upper) : ℝ :=
  (window.budget 2 + ∑' wave, decay wave) / 2

theorem ControlledWindow.majorant_control (window : ControlledWindow receipt lower upper)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    Summable (amplitude (velocity receipt time)) ∧
      (∑' wave, amplitude (velocity receipt time) wave) ≤ window.majorantBudget := by
  have paid := window.square_moments 2 time inside
  have summable := summable_moment_of_square (velocity receipt time) 0 paid.1
  have bound := moment_le_square_payment (velocity receipt time) 0 paid.1
  simp only [pow_zero, one_mul, Nat.zero_add] at summable bound
  refine ⟨summable, bound.trans ?_⟩
  exact div_le_div_of_nonneg_right (add_le_add paid.2 le_rfl) (by norm_num)

def ControlledWindow.fluxBudget (window : ControlledWindow receipt lower upper) (order : ℕ) : ℝ :=
  (2 * 2 ^ order) ^ 2 * window.majorantBudget ^ 2 * window.budget order

theorem ControlledWindow.flux_control (window : ControlledWindow receipt lower upper)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc window.first window.last) (output input : Coordinate) :
    Summable (fluxMomentDensity order (velocity receipt time) output input) ∧
      (∑' wave, fluxMomentDensity order (velocity receipt time) output input wave) ≤ window.fluxBudget order := by
  have majorant := window.majorant_control time inside
  have actual := flux_moment_control order (velocity receipt time) majorant.1 (window.paid order time inside) output input
  refine ⟨actual.1, actual.2.trans ?_⟩
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (tsum_nonneg (vorticityRowAmplitude_nonneg _)) majorant.2 2) (sq_nonneg _))
    (window.bound order time inside)
    (tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

def ControlledWindow.rateBudget (window : ControlledWindow receipt lower upper) (order : ℕ) : ℝ :=
  Real.sqrt (9 * (2 * Real.pi) ^ 2 * window.fluxBudget (order + 5)) +
    nu.coeff * (2 * Real.pi) ^ 2 * Real.sqrt (window.budget (order + 6))

theorem ControlledWindow.rate_decay (window : ControlledWindow receipt lower upper)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc window.first window.last) (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (rateRow receipt wave time) ≤ window.rateBudget order * decay wave := by
  let field := velocity receipt time
  let stress := quadraticFlux field
  have stressPaid := div_moment_control (order + 4) stress (window.fluxBudget (order + 5))
    (fun output input => window.flux_control (order + 5) time inside output input)
  have divDecay := weighted_row_decay (nativeFluidStressDivergenceCoefficient stress) order _ stressPaid.1 stressPaid.2 wave
  have nonnegative : 0 ≤ frequencySize wave ^ order := pow_nonneg (frequencySize_pos wave).le _
  have first := mul_le_mul_of_nonneg_left
    ((rowAmplitude_sub_le (transverseProjection wave (nativeFluidStressDivergenceCoefficient stress wave))
      ((nu.coeff * integerWaveViscousMultiplier wave) • field wave)).trans
        (add_le_add (rowAmplitude_projection_le wave (nativeFluidStressDivergenceCoefficient stress wave)) le_rfl)) nonnegative
  have coefficientNonnegative : 0 ≤ nu.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg nu.coeff_pos.le (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))
  rw [mul_add, rowAmplitude_real_smul, abs_of_nonneg coefficientNonnegative] at first
  have viscous : frequencySize wave ^ order * (nu.coeff * integerWaveViscousMultiplier wave * rowAmplitude (field wave)) ≤
      nu.coeff * (2 * Real.pi) ^ 2 * (Real.sqrt (window.budget (order + 6)) * decay wave) := by
    have gradient := mul_le_mul_of_nonneg_left (normSq_le_frequencySize_sq wave)
      (mul_nonneg (mul_nonneg nonnegative (mul_nonneg nu.coeff_pos.le (sq_nonneg (2 * Real.pi)))) (rowAmplitude_nonneg (field wave)))
    have decayed := mul_le_mul_of_nonneg_left (window.velocity_decay (order + 2) time inside wave)
      (mul_nonneg nu.coeff_pos.le (sq_nonneg (2 * Real.pi)))
    apply le_trans _ decayed
    unfold integerWaveViscousMultiplier
    convert! gradient using 1
    · ring
    · rw [pow_add]
      ring
  apply first.trans
  simpa only [ControlledWindow.rateBudget, add_mul, mul_assoc] using add_le_add divDecay viscous

def rate (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) (actual : ℝ) :
    ComplexVorticityHilbertState := ∑' wave, lp.single 2 wave (rateRow receipt wave actual)

theorem ControlledWindow.rate_summable (window : ControlledWindow receipt lower upper)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    Summable fun wave => (lp.single 2 wave (rateRow receipt wave time) : ComplexVorticityHilbertState) := by
  apply (decay_summable.mul_left (window.rateBudget 0)).of_norm_bounded
  intro wave
  rw [lp.norm_single (by norm_num)]
  apply (Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq _)).trans
  have paid := window.rate_decay 0 time inside wave
  simp only [pow_zero, one_mul] at paid
  convert! paid using 1

theorem ControlledWindow.rate_row (window : ControlledWindow receipt lower upper)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) (wave : IntegerWavevector) :
    rate receipt time wave = rateRow receipt wave time := by
  have read := (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).map_tsum
    (window.rate_summable time inside)
  change (lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave) (rate receipt time) = _
  rw [rate, read]
  change (∑' first, (lp.single 2 first (rateRow receipt first time) : ComplexVorticityHilbertState) wave) = _
  rw [tsum_eq_single wave]
  · exact lp.single_apply_self 2 _ _
  · intro first different
    exact lp.single_apply_ne 2 _ _ different.symm

theorem ControlledWindow.rate_continuous (window : ControlledWindow receipt lower upper) :
    ContinuousOn (rate receipt) (Icc window.first window.last) := by
  apply continuousOn_tsum
  · intro wave
    exact (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp_continuousOn
      (rateRow_continuousOn receipt _ window.velocity_continuous wave)
  · exact decay_summable.mul_left (window.rateBudget 0)
  · intro wave time inside
    rw [lp.norm_single (by norm_num)]
    apply (Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq _)).trans
    have paid := window.rate_decay 0 time inside wave
    simp only [pow_zero, one_mul] at paid
    convert! paid using 1

theorem ControlledWindow.velocity_hasDerivWithinAt (window : ControlledWindow receipt lower upper)
    (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    HasDerivWithinAt (velocity receipt) (rate receipt time) (Icc window.first window.last) time := by
  apply hilbert_hasDerivWithinAt_on_interval _ _ window.first window.last window.ordered.le
    window.velocity_continuous window.rate_continuous _ time inside
  intro wave sample member
  rw [window.rate_row sample member wave]
  exact window.row_hasDerivWithinAt wave sample member

theorem ControlledWindow.rate_moment_control (window : ControlledWindow receipt lower upper)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc window.first window.last) :
    Summable (velocityMomentDensity order (rate receipt time)) ∧
      (∑' wave, velocityMomentDensity order (rate receipt time) wave) ≤
        window.rateBudget order ^ 2 * (∑' wave, decay wave) ^ 2 := by
  have point (wave : IntegerWavevector) : velocityMomentDensity order (rate receipt time) wave ≤
      (window.rateBudget order ^ 2 * ∑' wave, decay wave) * decay wave := by
    have source := window.rate_decay order time inside wave
    have squared := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (frequencySize_pos wave).le _) (rowAmplitude_nonneg _)) source 2
    rw [mul_pow, mul_pow, rowAmplitude_sq] at squared
    have decayBound : decay wave ≤ ∑' actual, decay actual := decay_summable.le_tsum wave (fun _ _ => sq_nonneg _)
    have decaySquared : decay wave ^ 2 ≤ (∑' actual, decay actual) * decay wave := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right decayBound (show 0 ≤ decay wave from sq_nonneg _)
    change (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (rate receipt time wave) ≤ _
    rw [window.rate_row time inside wave, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    exact squared.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left decaySquared (sq_nonneg (window.rateBudget order)))
  have majorant := decay_summable.mul_left (window.rateBudget order ^ 2 * ∑' wave, decay wave)
  have paid := majorant.of_nonneg_of_le (fun _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) point
  refine ⟨paid, (paid.tsum_le_tsum point majorant).trans_eq ?_⟩
  rw [tsum_mul_left]
  ring

def sourceWindow (initial : GeneratedWholeRestartCurrent nu) :
    ControlledWindow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial)
      0 (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 :=
  generatedWindow (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) 0
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.1 le_rfl
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time_pos
    (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time.2.2

theorem sourceWindow_actual_time_derivative (initial : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (inside : time ∈ Icc (sourceWindow initial).first (sourceWindow initial).last) :
    HasDerivWithinAt (velocity (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial))
      (rate (sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial) time)
      (Icc (sourceWindow initial).first (sourceWindow initial).last) time :=
  (sourceWindow initial).velocity_hasDerivWithinAt time inside

end
end SaturationMonoid.NavierStokes.NativeRecoveryStrongWindow
