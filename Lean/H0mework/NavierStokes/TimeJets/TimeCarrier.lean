import H0mework.NavierStokes.TimeJets.TimeSource

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeTimeJetCarrier

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeFullOrderAction NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativeStressCurlAlgebra
open NativeFullOrderTime NativeHigherTimeJets NativeHigherTimeJetsSource

noncomputable section

abbrev Time (index : ℕ) := Icc (0 : ℝ) (run stackedShortCurrent index).duration

def zeroTime (index : ℕ) : Time index := ⟨0, le_rfl, (run stackedShortCurrent index).receipt.requestedTimePos.le⟩

def rawMoment (order : ℕ) (rows : IntegerWavevector → ComplexCoordinateVector) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (rows wave)

structure Profile (index : ℕ) where
  value : Time index → ComplexVorticityHilbertState
  budget : ℕ → ℝ
  continuous : Continuous value
  paid : ∀ order time, Summable (velocityMomentDensity order (value time))
  bound : ∀ order time, (∑' wave, velocityMomentDensity order (value time) wave) ≤ budget order

theorem Profile.budget_nonneg {index : ℕ} (profile : Profile index) (order : ℕ) : 0 ≤ profile.budget order :=
  (tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)).trans
    (profile.bound order (zeroTime index))

def Profile.majorantBudget {index : ℕ} (profile : Profile index) : ℝ :=
  (profile.budget 2 + ∑' wave, decay wave) / 2

theorem Profile.amplitude_summable {index : ℕ} (profile : Profile index) (time : Time index) :
    Summable (amplitude (profile.value time)) := by
  have paid := profile.paid 2 time
  unfold velocityMomentDensity at paid
  have second : Summable fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (profile.value time wave) := by
    simpa only [← pow_mul, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  simpa only [pow_zero, one_mul] using summable_moment_of_square (profile.value time) 0 second

theorem Profile.majorant_le {index : ℕ} (profile : Profile index) (time : Time index) :
    (∑' wave, amplitude (profile.value time) wave) ≤ profile.majorantBudget := by
  have paid := profile.paid 2 time
  unfold velocityMomentDensity at paid
  have second : Summable fun wave => frequencySize wave ^ (2 * (0 + 2)) *
      complexCoordinateAmplitudeSq (profile.value time wave) := by
    simpa only [← pow_mul, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  have source := moment_le_square_payment (profile.value time) 0 second
  simp only [pow_zero, one_mul] at source
  apply source.trans
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply add_le_add _ le_rfl
  simpa only [velocityMomentDensity, ← pow_mul, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
    profile.bound 2 time

theorem Profile.majorant_nonneg {index : ℕ} (profile : Profile index) : 0 ≤ profile.majorantBudget :=
  (tsum_nonneg (vorticityRowAmplitude_nonneg (profile.value (zeroTime index)))).trans
    (profile.majorant_le (zeroTime index))

private theorem rows_mem (rows : IntegerWavevector → ComplexCoordinateVector)
    (paid : Summable (rawMoment 0 rows)) : Memℓp rows 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply paid.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro wave
  simpa only [rawMoment, pow_zero, one_pow, one_mul,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
      complexCoordinateVector_norm_sq_le_amplitudeSq (rows wave)

def assemble {index : ℕ} (rows : Time index → IntegerWavevector → ComplexCoordinateVector) (budget : ℕ → ℝ)
    (rowsContinuous : ∀ wave, Continuous (fun time => rows time wave))
    (paid : ∀ order time, Summable (rawMoment order (rows time)))
    (bound : ∀ order time, (∑' wave, rawMoment order (rows time) wave) ≤ budget order) : Profile index where
  value time := ⟨rows time, rows_mem _ (paid 0 time)⟩
  budget := budget
  continuous := by
    let field (time) : ComplexVorticityHilbertState := ⟨rows time, rows_mem _ (paid 0 time)⟩
    have same : field = fun time => ∑' wave, (lp.single 2 wave (rows time wave) : ComplexVorticityHilbertState) := by
      funext time
      exact (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (field time)).tsum_eq.symm
    change Continuous field
    rw [same]
    apply continuous_tsum
    · intro wave
      exact (lp.singleContinuousLinearMap ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp (rowsContinuous wave)
    · exact decay_summable.mul_left (Real.sqrt (budget 4))
    · intro wave time
      rw [lp.norm_single (by norm_num)]
      apply (Real.le_sqrt_of_sq_le (complexCoordinateVector_norm_sq_le_amplitudeSq (rows time wave))).trans
      have pay : Summable fun wave => (frequencySize wave ^ (0 + 4)) ^ 2 * complexCoordinateAmplitudeSq (rows time wave) := by
        have payment := paid 4 time
        unfold rawMoment at payment
        simpa only [← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using payment
      have bounds : (∑' wave, (frequencySize wave ^ (0 + 4)) ^ 2 * complexCoordinateAmplitudeSq (rows time wave)) ≤ budget 4 := by
        simpa only [← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq, rawMoment] using bound 4 time
      have actual := weighted_row_decay (rows time) 0 (budget 4) pay bounds wave
      simp only [pow_zero, one_mul] at actual
      convert! actual using 1
  paid := paid
  bound := bound

@[simp] theorem assemble_row {index : ℕ} (rows : Time index → IntegerWavevector → ComplexCoordinateVector) (budget : ℕ → ℝ)
    (rowsContinuous : ∀ wave, Continuous (fun time => rows time wave))
    (paid : ∀ order time, Summable (rawMoment order (rows time)))
    (bound : ∀ order time, (∑' wave, rawMoment order (rows time) wave) ≤ budget order)
    (time : Time index) (wave : IntegerWavevector) :
    (assemble rows budget rowsContinuous paid bound).value time wave = rows time wave := rfl

def initial (index : ℕ) : Profile index where
  value time := wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath time)
  budget := fun order => runMomentBudget order index
  continuous := by
    have smoothOn : ContinuousOn (sourceVelocity index) (Icc (0 : ℝ) (run stackedShortCurrent index).duration) :=
      fun time inside => (sourceVelocity_hasDerivWithinAt index ⟨time, inside⟩).continuousWithinAt
    have restricted := smoothOn.domRestrict
    convert! restricted using 1
    funext time
    exact (sourceVelocity_on_interval index time).symm
  paid := fun order time => (run_receipt_moment_control order index time).1
  bound := fun order time => (run_receipt_moment_control order index time).2

theorem rowSq_add_le (left right : ComplexCoordinateVector) :
    complexCoordinateVectorNormSq (left + right) ≤ 2 * complexCoordinateVectorNormSq left + 2 * complexCoordinateVectorNormSq right := by
  have triangle : rowAmplitude (left + right) ≤ rowAmplitude left + rowAmplitude right := by
    rw [rowAmplitude_eq_norm, rowAmplitude_eq_norm, rowAmplitude_eq_norm]
    exact norm_add_le (WithLp.toLp 2 left : EuclideanSpace ℂ Coordinate) (WithLp.toLp 2 right)
  have squares := pow_le_pow_left₀ (rowAmplitude_nonneg _) triangle 2
  have difference := sq_nonneg (rowAmplitude left - rowAmplitude right)
  simp only [← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  nlinarith [rowAmplitude_sq left, rowAmplitude_sq right, rowAmplitude_sq (left + right)]

theorem rowSq_real_smul (scalar : ℝ) (row : ComplexCoordinateVector) :
    complexCoordinateVectorNormSq (scalar • row) = scalar ^ 2 * complexCoordinateVectorNormSq row := by
  have square := congrArg (fun value : ℝ => value ^ 2) (rowAmplitude_real_smul scalar row)
  simpa only [rowAmplitude_sq, mul_pow, sq_abs, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using square

private theorem add_density_le (order : ℕ) (left right : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    velocityMomentDensity order (left + right) wave ≤
      2 * velocityMomentDensity order left wave + 2 * velocityMomentDensity order right wave := by
  have scaled := mul_le_mul_of_nonneg_left (rowSq_add_le (left wave) (right wave)) (sq_nonneg (frequencySize wave ^ order))
  change (frequencySize wave ^ order) ^ 2 * complexCoordinateVectorNormSq (left wave + right wave) ≤ _
  unfold velocityMomentDensity
  nlinarith

def add {index : ℕ} (left right : Profile index) : Profile index where
  value time := left.value time + right.value time
  budget order := 2 * left.budget order + 2 * right.budget order
  continuous := left.continuous.add right.continuous
  paid order time :=
    (((left.paid order time).mul_left 2).add ((right.paid order time).mul_left 2)).of_nonneg_of_le
      (fun _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _))
      (add_density_le order (left.value time) (right.value time))
  bound order time := by
    have l := left.paid order time
    have r := right.paid order time
    have source := (l.mul_left 2).add (r.mul_left 2)
    have newPaid := source.of_nonneg_of_le
      (fun wave => mul_nonneg (sq_nonneg (frequencySize wave ^ order)) (complexCoordinateVectorNormSq_nonneg (left.value time wave + right.value time wave)))
      (add_density_le order (left.value time) (right.value time))
    have written := newPaid.tsum_le_tsum (add_density_le order (left.value time) (right.value time)) source
    rw [(l.mul_left 2).tsum_add (r.mul_left 2), tsum_mul_left, tsum_mul_left] at written
    linarith [left.bound order time, right.bound order time]

private theorem scale_density (scalar : ℝ) (order : ℕ) (field : ComplexVorticityHilbertState) :
    velocityMomentDensity order (scalar • field) = fun wave => scalar ^ 2 * velocityMomentDensity order field wave := by
  funext wave
  simp only [velocityMomentDensity, lp.coeFn_smul, Pi.smul_apply, rowSq_real_smul]
  ring

def scale {index : ℕ} (scalar : ℝ) (profile : Profile index) : Profile index where
  value time := scalar • profile.value time
  budget order := scalar ^ 2 * profile.budget order
  continuous := profile.continuous.const_smul scalar
  paid order time := by
    rw [scale_density]
    exact (profile.paid order time).mul_left _
  bound order time := by
    rw [scale_density, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (profile.bound order time) (sq_nonneg _)

def zero (index : ℕ) : Profile index where
  value _ := 0
  budget _ := 0
  continuous := continuous_const
  paid order time := by
    unfold velocityMomentDensity
    simp only [lp.coeFn_zero, Pi.zero_apply, complexCoordinateVectorNormSq, map_zero, Finset.sum_const_zero, mul_zero]
    exact summable_zero
  bound order time := by
    simp [velocityMomentDensity, complexCoordinateVectorNormSq]

def sum {index : ℕ} (profiles : List (Profile index)) : Profile index := profiles.foldr add (zero index)

theorem sum_value {index : ℕ} (profiles : List (Profile index)) (time : Time index) :
    (sum profiles).value time = (profiles.map fun profile => profile.value time).sum := by
  induction profiles with
  | nil => rfl
  | cons head tail ih =>
    change head.value time + (sum tail).value time = _
    rw [ih]
    rfl

theorem sum_ofFn_value {index count : ℕ} (profiles : Fin count → Profile index) (time : Time index) :
    (sum (List.ofFn profiles)).value time = ∑ rank : Fin count, (profiles rank).value time := by
  rw [sum_value, List.map_ofFn, List.sum_ofFn]
  rfl

def mixedBudget {index : ℕ} (left right : Profile index) (order : ℕ) : ℝ :=
  2 * (2 ^ order) ^ 2 *
    (right.majorantBudget ^ 2 * left.budget order + left.majorantBudget ^ 2 * right.budget order)

theorem mixedBudget_bound {index : ℕ} (left right : Profile index) (order : ℕ) (time : Time index) :
    mixedMomentBudget order (left.value time) (right.value time) ≤ mixedBudget left right order := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · exact mul_le_mul
      (pow_le_pow_left₀ (tsum_nonneg (vorticityRowAmplitude_nonneg _)) (right.majorant_le time) 2)
      (left.bound order time)
      (tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) (sq_nonneg _)
  · exact mul_le_mul
      (pow_le_pow_left₀ (tsum_nonneg (vorticityRowAmplitude_nonneg _)) (left.majorant_le time) 2)
      (right.bound order time)
      (tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) (sq_nonneg _)

def projectedDivergenceCLM (wave : IntegerWavevector) : NativeFluidStressCoefficient →L[ℝ] ComplexCoordinateVector :=
  (transverseProjectionCLM wave).comp ((stressDivergenceCLM wave).restrictScalars ℝ)

theorem projectedDivergenceCLM_apply (wave : IntegerWavevector) (stress : NativeFluidStressCoefficient) :
    projectedDivergenceCLM wave stress =
      transverseProjection wave (nativeFluidStressDivergenceCoefficient (fun _ => stress) wave) := rfl

def bilinear {index : ℕ} (left right : Profile index) : Profile index := by
  let rows (time : Time index) (wave : IntegerWavevector) :=
    projectedDivergenceCLM wave (mixedFlux (left.value time) (right.value time) wave)
  let budget order := 9 * (2 * Real.pi) ^ 2 * mixedBudget left right (order + 1)
  have controls (order : ℕ) (time : Time index) : Summable (rawMoment order (rows time)) ∧
      (∑' wave, rawMoment order (rows time) wave) ≤ budget order := by
    have stressPaid (output input : Coordinate) :
        Summable (stressDensity (order + 1) (mixedFlux (left.value time) (right.value time)) output input) ∧
          (∑' wave, stressDensity (order + 1) (mixedFlux (left.value time) (right.value time)) output input wave) ≤
            mixedBudget left right (order + 1) := by
      have actual := mixed_moment_control (order + 1) (left.value time) (right.value time)
        (left.amplitude_summable time) (right.amplitude_summable time)
        (left.paid (order + 1) time) (right.paid (order + 1) time) output input
      exact ⟨actual.1, actual.2.trans (mixedBudget_bound left right (order + 1) time)⟩
    have divergence := div_moment_control order (mixedFlux (left.value time) (right.value time))
      (mixedBudget left right (order + 1)) stressPaid
    have pointwise wave : rawMoment order (rows time) wave ≤ divDensity order (mixedFlux (left.value time) (right.value time)) wave := by
      have contraction := pow_le_pow_left₀ (rowAmplitude_nonneg _)
        (rowAmplitude_projection_le wave (nativeFluidStressDivergenceCoefficient (mixedFlux (left.value time) (right.value time)) wave)) 2
      simp only [rowAmplitude_sq, complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] at contraction
      simp only [rawMoment, divDensity, rows, projectedDivergenceCLM_apply,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      exact mul_le_mul_of_nonneg_left contraction (sq_nonneg _)
    have paid := divergence.1.of_nonneg_of_le
      (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) pointwise
    exact ⟨paid, (paid.tsum_le_tsum pointwise divergence.1).trans divergence.2⟩
  apply assemble rows budget _ (fun order time => (controls order time).1) (fun order time => (controls order time).2)
  intro wave
  apply (projectedDivergenceCLM wave).continuous.comp
  apply continuous_pi
  intro output
  apply continuous_pi
  intro input
  exact ((mixedFluxCLM wave output input).continuous.comp left.continuous).clm_apply right.continuous

@[simp] theorem bilinear_row {index : ℕ} (left right : Profile index) (time : Time index) (wave : IntegerWavevector) :
    (bilinear left right).value time wave = projectedDivergenceCLM wave (mixedFlux (left.value time) (right.value time) wave) := rfl

@[simp] theorem bilinear_budget {index : ℕ} (left right : Profile index) (order : ℕ) :
    (bilinear left right).budget order = 9 * (2 * Real.pi) ^ 2 * mixedBudget left right (order + 1) := rfl

theorem viscous_density_le (viscosity : ℝ) (order : ℕ) (rows : IntegerWavevector → ComplexCoordinateVector)
    (wave : IntegerWavevector) :
    rawMoment order (fun frequency => -(viscosity * integerWaveViscousMultiplier frequency) • rows frequency) wave ≤
      viscosity ^ 2 * (2 * Real.pi) ^ 4 * rawMoment (order + 2) rows wave := by
  have lambdaSquare := pow_le_pow_left₀ (integerWaveNormSq_nonneg wave) (normSq_le_frequencySize_sq wave) 2
  have scaled := mul_le_mul_of_nonneg_left lambdaSquare
    (mul_nonneg (mul_nonneg (sq_nonneg (frequencySize wave ^ order))
      (mul_nonneg (sq_nonneg viscosity) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) 4)))
      (complexCoordinateVectorNormSq_nonneg (rows wave)))
  unfold rawMoment
  rw [rowSq_real_smul]
  unfold integerWaveViscousMultiplier
  convert! scaled using 1
  · ring
  · rw [pow_add]
    ring

def viscous {index : ℕ} (profile : Profile index) : Profile index := by
  let rows (time : Time index) (wave : IntegerWavevector) :=
    -(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • profile.value time wave
  let budget order := butterflyGainViscosity.coeff ^ 2 * (2 * Real.pi) ^ 4 * profile.budget (order + 2)
  have controls (order : ℕ) (time : Time index) : Summable (rawMoment order (rows time)) ∧
      (∑' wave, rawMoment order (rows time) wave) ≤ budget order := by
    have source := (profile.paid (order + 2) time).mul_left (butterflyGainViscosity.coeff ^ 2 * (2 * Real.pi) ^ 4)
    have pointwise := viscous_density_le butterflyGainViscosity.coeff order (profile.value time)
    have paid := source.of_nonneg_of_le
      (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) pointwise
    refine ⟨paid, ?_⟩
    have actual := paid.tsum_le_tsum pointwise source
    rw [tsum_mul_left] at actual
    exact actual.trans (mul_le_mul_of_nonneg_left (profile.bound (order + 2) time)
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) 4)))
  apply assemble rows budget _ (fun order time => (controls order time).1) (fun order time => (controls order time).2)
  intro wave
  exact ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp profile.continuous).const_smul
    (-(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave))

@[simp] theorem viscous_row {index : ℕ} (profile : Profile index) (time : Time index) (wave : IntegerWavevector) :
    (viscous profile).value time wave = -(butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • profile.value time wave := rfl

@[simp] theorem viscous_budget {index : ℕ} (profile : Profile index) (order : ℕ) :
    (viscous profile).budget order = butterflyGainViscosity.coeff ^ 2 * (2 * Real.pi) ^ 4 * profile.budget (order + 2) := rfl

end
end SaturationMonoid.NavierStokes.NativeTimeJetCarrier
