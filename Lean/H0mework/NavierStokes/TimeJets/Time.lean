import H0mework.NavierStokes.SourceAction.Consumer
import H0mework.NavierStokes.SourceAction.Flux
import H0mework.NavierStokes.SourceReadout.TimeAction
import H0mework.NavierStokes.VelocityGalerkin.FiniteObservationTimeTightness
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeFullOrderTime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativePhysicalFourier NativePhysicalContinuous
open NativeFullOrderAction NativeFullOrderNext NativeFullOrderSynthesis NativeFullOrderFlux NativeFullOrderStress

noncomputable section

def clamp (T : ℝ) (positive : 0 < T) (time : ℝ) : ℝ :=
  (projIcc (0 : ℝ) T positive.le time).1

theorem clamp_continuous (T : ℝ) (positive : 0 < T) : Continuous (clamp T positive) :=
  continuous_subtype_val.comp continuous_projIcc

theorem clamp_mem (T : ℝ) (positive : 0 < T) (time : ℝ) : clamp T positive time ∈ Icc (0 : ℝ) T :=
  (projIcc (0 : ℝ) T positive.le time).2

theorem clamp_of_mem {T : ℝ} (positive : 0 < T) {time : ℝ} (inside : time ∈ Icc (0 : ℝ) T) :
    clamp T positive time = time := by
  simp only [clamp, projIcc_of_mem positive.le inside]

theorem hasDerivWithinAt_tsum_Icc {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (positive : 0 < T) (field rate : ι → ℝ → E) (fieldBound rateBound : ι → ℝ)
    (fieldPaid : Summable fieldBound) (ratePaid : Summable rateBound)
    (evolves : ∀ index time, time ∈ Icc (0 : ℝ) T → HasDerivAt (field index) (rate index time) time)
    (rateContinuous : ∀ index, ContinuousOn (rate index) (Icc (0 : ℝ) T))
    (fieldBounded : ∀ index time, time ∈ Icc (0 : ℝ) T → ‖field index time‖ ≤ fieldBound index)
    (rateBounded : ∀ index time, time ∈ Icc (0 : ℝ) T → ‖rate index time‖ ≤ rateBound index)
    (time : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun actual => ∑' index, field index (clamp T positive actual))
      (∑' index, rate index time.1) (Icc (0 : ℝ) T) time.1 := by
  let F := fun actual => ∑' index, field index (clamp T positive actual)
  let G := fun actual => ∑' index, rate index (clamp T positive actual)
  have fieldContinuous (index) : ContinuousOn (field index) (Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn (evolves index)
  have FContinuous : Continuous F := by
    apply continuous_tsum
    · intro index
      exact (fieldContinuous index).comp_continuous (clamp_continuous T positive) (clamp_mem T positive)
    · exact fieldPaid
    · intro index actual
      exact fieldBounded index _ (clamp_mem T positive actual)
  have GContinuous : Continuous G := by
    apply continuous_tsum
    · intro index
      exact (rateContinuous index).comp_continuous (clamp_continuous T positive) (clamp_mem T positive)
    · exact ratePaid
    · intro index actual
      exact rateBounded index _ (clamp_mem T positive actual)
  have interior (actual : ℝ) (inside : actual ∈ Ioo (0 : ℝ) T) : HasDerivAt F (G actual) actual := by
    have within := Ioo_subset_Icc_self inside
    have series := hasDerivAt_tsum_of_isPreconnected ratePaid isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
      (fun index sample member => evolves index sample (Ioo_subset_Icc_self member))
      (fun index sample member => rateBounded index sample (Ioo_subset_Icc_self member)) inside
      (fieldPaid.of_norm_bounded fun index => fieldBounded index actual within) inside
    have same : F =ᶠ[𝓝 actual] fun sample => ∑' index, field index sample := by
      filter_upwards [isOpen_Ioo.mem_nhds inside] with sample member
      dsimp [F]
      rw [clamp_of_mem positive (Ioo_subset_Icc_self member)]
    have output : G actual = ∑' index, rate index actual := by
      dsimp [G]
      rw [clamp_of_mem positive within]
    rw [output]
    exact series.congr_of_eventuallyEq same
  have derivativeContinuous : Continuous (fun actual => (ContinuousLinearMap.smulRightL ℝ ℝ E 1) (G actual)) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E 1).continuous.comp GContinuous
  have limit : Tendsto (fun actual => fderiv ℝ F actual) (𝓝[Ioo (0 : ℝ) T] time.1)
      (𝓝 ((ContinuousLinearMap.smulRightL ℝ ℝ E 1) (G time.1))) := by
    apply ((derivativeContinuous.tendsto time.1).mono_left inf_le_left).congr'
    filter_upwards [self_mem_nhdsWithin] with actual inside
    exact (interior actual inside).hasFDerivAt.fderiv.symm
  have complete := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun actual inside => (interior actual inside).differentiableAt.differentiableWithinAt)
    (convex_Ioo (0 : ℝ) T) isOpen_Ioo
    (fun actual _ => FContinuous.continuousAt.continuousWithinAt) limit
  rw [closure_Ioo positive.ne] at complete
  have actual : G time.1 = ∑' index, rate index time.1 := by
    dsimp [G]
    rw [clamp_of_mem positive time.2]
  rw [← actual]
  exact complete

def rowAmplitude (row : ComplexCoordinateVector) : ℝ := Real.sqrt (complexCoordinateAmplitudeSq row)

theorem rowAmplitude_nonneg (row : ComplexCoordinateVector) : 0 ≤ rowAmplitude row := Real.sqrt_nonneg _

theorem rowAmplitude_sq (row : ComplexCoordinateVector) : rowAmplitude row ^ 2 = complexCoordinateAmplitudeSq row :=
  Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg row)

theorem weighted_row_decay (rows : IntegerWavevector → ComplexCoordinateVector) (order : ℕ) (budget : ℝ)
    (paid : Summable fun wave => (frequencySize wave ^ (order + 4)) ^ 2 * complexCoordinateAmplitudeSq (rows wave))
    (bound : (∑' wave, (frequencySize wave ^ (order + 4)) ^ 2 * complexCoordinateAmplitudeSq (rows wave)) ≤ budget)
    (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (rows wave) ≤ Real.sqrt budget * decay wave := by
  have nonnegative index : 0 ≤ (frequencySize index ^ (order + 4)) ^ 2 * complexCoordinateAmplitudeSq (rows index) :=
    mul_nonneg (sq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _)
  have rowBound := paid.sum_le_tsum {wave} (fun index _ => nonnegative index)
  simp only [Finset.sum_singleton] at rowBound
  have term := rowBound.trans bound
  have square : (frequencySize wave ^ (order + 4) * rowAmplitude (rows wave)) ^ 2 ≤ budget := by
    simpa only [mul_pow, rowAmplitude_sq] using term
  have root := Real.le_sqrt_of_sq_le square
  have paidDecay := mul_le_mul_of_nonneg_right root (sq_nonneg ((frequencySize wave ^ 2)⁻¹))
  apply le_trans _ paidDecay
  apply le_of_eq
  rw [pow_add]
  have nonzero := (frequencySize_pos wave).ne'
  field_simp

def rowValue (z : ℂ) (row : ComplexCoordinateVector) : PhysicalSpace :=
  WithLp.toLp 2 fun coordinate => (row coordinate * z).re

def rowValueCLM (z : ℂ) : ComplexCoordinateVector →L[ℝ] PhysicalSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := rowValue z
      map_add' := by
        intro a b
        apply PiLp.ext
        intro coordinate
        simp [rowValue, add_mul]
      map_smul' := by
        intro scalar row
        apply PiLp.ext
        intro coordinate
        simp [rowValue, Complex.real_smul, mul_comm]
        ring }

theorem rowValue_norm_le (z : ℂ) (row : ComplexCoordinateVector) :
    ‖rowValueCLM z row‖ ≤ ‖z‖ * rowAmplitude row := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (rowAmplitude_nonneg _))).mp
  change ‖rowValue z row‖ ^ 2 ≤ _
  rw [mul_pow, rowAmplitude_sq, EuclideanSpace.norm_sq_eq]
  unfold complexCoordinateAmplitudeSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro coordinate _
  change ‖(row coordinate * z).re‖ ^ 2 ≤ _
  rw [Complex.normSq_eq_norm_sq, mul_comm (‖z‖ ^ 2), ← mul_pow, ← norm_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (Complex.abs_re_le_norm _)

def wordScalar (order : ℕ) (directions : Fin order → PhysicalSpace)
    (wave : IntegerWavevector) (point : PhysicalSpace) : ℂ :=
  (∏ index, phase wave (directions index)) • (Complex.I ^ order * monomial wave point)

def wordNorm (order : ℕ) (directions : Fin order → PhysicalSpace) : ℝ :=
  (2 * Real.pi) ^ order * ∏ index, ‖directions index‖

theorem wordNorm_nonneg (order : ℕ) (directions : Fin order → PhysicalSpace) : 0 ≤ wordNorm order directions := by
  unfold wordNorm
  positivity

theorem wordScalar_norm_le (order : ℕ) (directions : Fin order → PhysicalSpace)
    (wave : IntegerWavevector) (point : PhysicalSpace) :
    ‖wordScalar order directions wave point‖ ≤ wordNorm order directions * frequencySize wave ^ order := by
  have monomialNorm : ‖monomial wave point‖ = 1 := by
    rw [monomial, monomial_phase]
    simp [profile, Complex.norm_exp]
  have each (index : Fin order) : |phase wave (directions index)| ≤
      (2 * Real.pi * frequencySize wave) * ‖directions index‖ :=
    ((phase wave).le_opNorm (directions index)).trans
      (mul_le_mul_of_nonneg_right (phase_norm_le wave) (norm_nonneg _))
  have finite := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin order)))
    (fun index _ => abs_nonneg (phase wave (directions index))) (fun index _ => each index)
  unfold wordScalar
  simp only [norm_smul, norm_mul, norm_pow, Complex.norm_I, one_pow, monomialNorm,
    mul_one, Real.norm_eq_abs, Finset.abs_prod]
  apply finite.trans_eq
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    wordNorm, mul_pow]
  ring

def observeWord (order : ℕ) (directions : Fin order → PhysicalSpace)
    (wave : IntegerWavevector) (point : PhysicalSpace) : ComplexCoordinateVector →L[ℝ] PhysicalSpace :=
  rowValueCLM (wordScalar order directions wave point)

theorem observeWord_norm_le (order : ℕ) (directions : Fin order → PhysicalSpace)
    (wave : IntegerWavevector) (point : PhysicalSpace) (row : ComplexCoordinateVector) :
    ‖observeWord order directions wave point row‖ ≤
      wordNorm order directions * (frequencySize wave ^ order * rowAmplitude row) := by
  apply (rowValue_norm_le _ row).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (wordScalar_norm_le order directions wave point) (rowAmplitude_nonneg row)

theorem receipt_velocity_row_hasDerivAt {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) T) :
    HasDerivAt (receiptVelocityRow receipt wave) (receiptMomentumAction receipt wave time.1) time.1 := by
  by_cases nonzero : wave ≠ 0
  · have actual := (biotSavartVelocityCLM wave).hasFDerivAt.comp_hasDerivAt time.1
      (receipt_vorticity_hasDerivAt receipt wave nonzero time)
    have same : (actualWholeProjectedTransversePath receipt time.1).1 = receipt.wholePath time := by
      change receipt.wholePath (projIcc (0 : ℝ) T receipt.requestedTimePos.le time.1) = _
      rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
    rw [receiptMomentumAction, same]
    convert! actual using 1
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    unfold receiptVelocityRow receiptMomentumAction
    simp only [biotSavartVelocityCoefficient_zero]
    convert! (hasDerivAt_const time.1 (0 : ComplexCoordinateVector)) using 1

theorem receipt_velocity_row_eq {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial T) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) T) :
    receiptVelocityRow receipt wave time.1 = wholeBiotSavartVelocityState (receipt.wholePath time) wave := by
  by_cases nonzero : wave ≠ 0
  · exact receiptVelocityRow_eq receipt wave nonzero time
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [receiptVelocityRow, wholeBiotSavartVelocityState_apply, finiteStateVelocityCoefficient]

theorem rowAmplitude_eq_norm (row : ComplexCoordinateVector) :
    rowAmplitude row = ‖(WithLp.toLp 2 row : EuclideanSpace ℂ Coordinate)‖ := by
  have square : ‖(WithLp.toLp 2 row : EuclideanSpace ℂ Coordinate)‖ ^ 2 = complexCoordinateAmplitudeSq row := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [complexCoordinateAmplitudeSq, Complex.normSq_eq_norm_sq]
  rw [rowAmplitude, ← square, Real.sqrt_sq (norm_nonneg _)]

theorem rowAmplitude_sub_le (left right : ComplexCoordinateVector) :
    rowAmplitude (left - right) ≤ rowAmplitude left + rowAmplitude right := by
  rw [rowAmplitude_eq_norm, rowAmplitude_eq_norm, rowAmplitude_eq_norm]
  exact norm_sub_le (WithLp.toLp 2 left : EuclideanSpace ℂ Coordinate) (WithLp.toLp 2 right)

theorem rowAmplitude_real_smul (scalar : ℝ) (row : ComplexCoordinateVector) :
    rowAmplitude (scalar • row) = |scalar| * rowAmplitude row := by
  rw [rowAmplitude_eq_norm, rowAmplitude_eq_norm]
  exact norm_smul scalar (WithLp.toLp 2 row : EuclideanSpace ℂ Coordinate)

theorem rowAmplitude_projection_le (wave : IntegerWavevector) (row : ComplexCoordinateVector) :
    rowAmplitude (transverseProjection wave row) ≤ rowAmplitude row := by
  by_cases zero : wave = 0
  · subst wave
    simp [transverseProjection, rowAmplitude, complexCoordinateAmplitudeSq]
  · apply (sq_le_sq₀ (rowAmplitude_nonneg _) (rowAmplitude_nonneg _)).mp
    rw [rowAmplitude_sq, rowAmplitude_sq]
    exact transverseProjection_amplitudeSq_le wave zero row

def divDensity (order : ℕ) (stress : NativeFluidStressFourierState) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * complexCoordinateAmplitudeSq (nativeFluidStressDivergenceCoefficient stress wave)

def stressDensity (order : ℕ) (stress : NativeFluidStressFourierState)
    (output input : Coordinate) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * Complex.normSq (stress wave output input)

theorem divDensity_row_le (order : ℕ) (stress : NativeFluidStressFourierState) (wave : IntegerWavevector) :
    divDensity order stress wave ≤ (2 * Real.pi) ^ 2 *
      ∑ output : Coordinate, ∑ input : Coordinate, stressDensity (order + 1) stress output input wave := by
  have multiplier : integerWaveViscousMultiplier wave ≤ (2 * Real.pi) ^ 2 * frequencySize wave ^ 2 :=
    mul_le_mul_of_nonneg_left (normSq_le_frequencySize_sq wave) (sq_nonneg _)
  have row := (divergence_amplitude_le stress wave).trans
    (mul_le_mul_of_nonneg_right multiplier
      (Finset.sum_nonneg fun output _ => Finset.sum_nonneg fun input _ => Complex.normSq_nonneg _))
  have weighted := mul_le_mul_of_nonneg_left row (sq_nonneg (frequencySize wave ^ order))
  unfold divDensity stressDensity
  simp only [← Finset.mul_sum]
  convert! weighted using 1
  rw [pow_succ]
  ring

theorem div_moment_control (order : ℕ) (stress : NativeFluidStressFourierState) (budget : ℝ)
    (paid : ∀ output input : Coordinate, Summable (stressDensity (order + 1) stress output input) ∧
      (∑' wave, stressDensity (order + 1) stress output input wave) ≤ budget) :
    Summable (divDensity order stress) ∧ (∑' wave, divDensity order stress wave) ≤ 9 * (2 * Real.pi) ^ 2 * budget := by
  have totalPaid : Summable fun wave =>
      ∑ output : Coordinate, ∑ input : Coordinate, stressDensity (order + 1) stress output input wave :=
    summable_sum fun output _ => summable_sum fun input _ => (paid output input).1
  have generated := (totalPaid.mul_left ((2 * Real.pi) ^ 2)).of_nonneg_of_le
    (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _)) (divDensity_row_le order stress)
  refine ⟨generated, ?_⟩
  have bound := generated.tsum_le_tsum (divDensity_row_le order stress) (totalPaid.mul_left ((2 * Real.pi) ^ 2))
  rw [tsum_mul_left, Summable.tsum_finsetSum
    (fun output _ => summable_sum fun input _ => (paid output input).1)] at bound
  apply bound.trans
  have each (output : Coordinate) :
      (∑' wave, ∑ input : Coordinate, stressDensity (order + 1) stress output input wave) ≤ 3 * budget := by
    rw [Summable.tsum_finsetSum (fun input _ => (paid output input).1)]
    simpa using Finset.sum_le_sum fun input (_ : input ∈ (Finset.univ : Finset Coordinate)) => (paid output input).2
  have total := Finset.sum_le_sum fun output (_ : output ∈ (Finset.univ : Finset Coordinate)) => each output
  have scaled := mul_le_mul_of_nonneg_left total (sq_nonneg (2 * Real.pi))
  apply scaled.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def rateBudget (order index : ℕ) : ℝ :=
  Real.sqrt (9 * (2 * Real.pi) ^ 2 * sourceFluxBudget (order + 5) index) +
    butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 * Real.sqrt (runMomentBudget (order + 6) index)

theorem run_velocity_decay (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (wholeBiotSavartVelocityState
      ((run stackedShortCurrent index).receipt.wholePath time) wave) ≤
      Real.sqrt (runMomentBudget (order + 4) index) * decay wave := by
  have source := run_receipt_moment_control (order + 4) index time
  apply weighted_row_decay _ order _ _ _ wave
  · have paid := source.1
    unfold momentDensity at paid
    simpa only [wholeBiotSavartVelocityState_apply,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid
  · simpa only [moment, momentDensity, wholeBiotSavartVelocityState_apply,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using source.2

theorem run_momentum_decay (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (wave : IntegerWavevector) :
    frequencySize wave ^ order * rowAmplitude (receiptMomentumAction
      (run stackedShortCurrent index).receipt wave time.1) ≤ rateBudget order index * decay wave := by
  let receipt := (run stackedShortCurrent index).receipt
  let state := receipt.wholePath time
  let velocity := wholeBiotSavartVelocityState state
  let stress := quadraticFlux velocity
  have stressPaid := div_moment_control (order + 4) stress (sourceFluxBudget (order + 5) index)
    (fun output input => run_receipt_flux_control (order + 5) index time output input)
  have divDecay := weighted_row_decay (nativeFluidStressDivergenceCoefficient stress) order _ stressPaid.1 stressPaid.2 wave
  have same : (actualWholeProjectedTransversePath receipt time.1).1 = state := by
    change receipt.wholePath (projIcc (0 : ℝ) _ receipt.requestedTimePos.le time.1) = _
    rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
  have rate : receiptMomentumAction receipt wave time.1 =
      transverseProjection wave (nativeFluidStressDivergenceCoefficient stress wave) -
        (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • velocity wave := by
    rw [receiptMomentumAction, same]
    by_cases nonzero : wave ≠ 0
    · unfold wholeLatticeVorticityFourierTangentAt
      change (biotSavartVelocityCLM wave) (_ - _ • state wave) = _
      rw [map_sub, map_smul, biotSavartVelocityCLM_apply]
      rw [← quadraticFlux_biotSavart_action state (receipt.wholePath_zero_row time)
        (wholePath_transverse receipt time) wave, nativeFluidConstitutiveVorticityAction,
        biotSavartVelocityCoefficient_fourierCurlCoefficient wave _ nonzero]
      rfl
    · have zero : wave = 0 := not_ne_iff.mp nonzero
      subst wave
      simp [transverseProjection, integerWaveViscousMultiplier]
  rw [rate]
  have nonnegative : 0 ≤ frequencySize wave ^ order := pow_nonneg (frequencySize_pos wave).le _
  have first := mul_le_mul_of_nonneg_left
    ((rowAmplitude_sub_le (transverseProjection wave (nativeFluidStressDivergenceCoefficient stress wave))
      ((butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • velocity wave)).trans
        (add_le_add (rowAmplitude_projection_le wave (nativeFluidStressDivergenceCoefficient stress wave)) le_rfl)) nonnegative
  rw [mul_add, rowAmplitude_real_smul] at first
  have coefficientNonneg : 0 ≤ butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave :=
    mul_nonneg butterflyGainViscosity.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg _))
  rw [abs_of_nonneg coefficientNonneg] at first
  have viscous : frequencySize wave ^ order *
      (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave * rowAmplitude (velocity wave)) ≤
        butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 *
          (Real.sqrt (runMomentBudget (order + 6) index) * decay wave) := by
    have gradient := mul_le_mul_of_nonneg_left (normSq_le_frequencySize_sq wave)
      (mul_nonneg (mul_nonneg nonnegative (mul_nonneg butterflyGainViscosity.coeff_pos.le (sq_nonneg (2 * Real.pi))))
        (rowAmplitude_nonneg (velocity wave)))
    have decayed := mul_le_mul_of_nonneg_left (run_velocity_decay (order + 2) index time wave)
      (mul_nonneg butterflyGainViscosity.coeff_pos.le (sq_nonneg (2 * Real.pi)))
    apply le_trans _ decayed
    unfold integerWaveViscousMultiplier
    convert! gradient using 1
    · ring
    · rw [pow_add]
      ring
  apply first.trans
  have result := add_le_add divDecay viscous
  simpa only [rateBudget, add_mul, mul_assoc] using result

def spatialWord (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  iteratedFDeriv ℝ order
    (spatialField (wholeBiotSavartVelocityState ((run stackedShortCurrent index).receipt.wholePath
      (projIcc (0 : ℝ) _ (run stackedShortCurrent index).receipt.requestedTimePos.le actual)))) point directions

def wordRate (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  ∑' wave, observeWord order directions wave point
    (receiptMomentumAction (run stackedShortCurrent index).receipt wave actual)

theorem spatialWord_eq_sum (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) :
    spatialWord index order directions point = fun actual => ∑' wave,
      observeWord order directions wave point (receiptVelocityRow (run stackedShortCurrent index).receipt wave
        (clamp (run stackedShortCurrent index).duration (run stackedShortCurrent index).receipt.requestedTimePos actual)) := by
  funext actual
  let time := projIcc (0 : ℝ) (run stackedShortCurrent index).duration
    (run stackedShortCurrent index).receipt.requestedTimePos.le actual
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have regular := run_receipt_momentRegular index time
  have moments (order : ℕ) : Summable fun wave => frequencySize wave ^ order * amplitude (wholeBiotSavartVelocityState state) wave := by
    apply summable_moment_of_square
    rw [source_square_moment_eq]
    exact regular (order + 2)
  change iteratedFDeriv ℝ order (spatialField (wholeBiotSavartVelocityState state)) point directions = _
  rw [spatialField_word_eq _ moments]
  apply tsum_congr
  intro wave
  change value (wholeBiotSavartVelocityState state) wave (wordScalar order directions wave point) =
    observeWord order directions wave point (receiptVelocityRow (run stackedShortCurrent index).receipt wave time.1)
  rw [receipt_velocity_row_eq _ wave time]
  rfl

theorem observed_velocity_bound (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ‖observeWord order directions wave point (receiptVelocityRow (run stackedShortCurrent index).receipt wave time.1)‖ ≤
      (wordNorm order directions * Real.sqrt (runMomentBudget (order + 4) index)) * decay wave := by
  rw [receipt_velocity_row_eq _ wave time]
  apply (observeWord_norm_le order directions wave point _).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (run_velocity_decay order index time wave)
    (wordNorm_nonneg order directions)

theorem observed_rate_bound (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ‖observeWord order directions wave point (receiptMomentumAction (run stackedShortCurrent index).receipt wave time.1)‖ ≤
      (wordNorm order directions * rateBudget order index) * decay wave := by
  apply (observeWord_norm_le order directions wave point _).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (run_momentum_decay order index time wave)
    (wordNorm_nonneg order directions)

theorem run_spatialWord_hasDerivWithinAt (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    HasDerivWithinAt (spatialWord index order directions point) (wordRate index order directions point time.1)
      (Icc (0 : ℝ) (run stackedShortCurrent index).duration) time.1 := by
  let receipt := (run stackedShortCurrent index).receipt
  have actual := hasDerivWithinAt_tsum_Icc _ receipt.requestedTimePos
    (fun wave sample => observeWord order directions wave point (receiptVelocityRow receipt wave sample))
    (fun wave sample => observeWord order directions wave point (receiptMomentumAction receipt wave sample))
    (fun wave => (wordNorm order directions * Real.sqrt (runMomentBudget (order + 4) index)) * decay wave)
    (fun wave => (wordNorm order directions * rateBudget order index) * decay wave)
    (decay_summable.mul_left _) (decay_summable.mul_left _)
    (fun wave sample inside => (observeWord order directions wave point).hasFDerivAt.comp_hasDerivAt sample
      (receipt_velocity_row_hasDerivAt receipt wave ⟨sample, inside⟩))
    (fun wave => ((observeWord order directions wave point).continuous.comp
      (receiptMomentumAction_continuous receipt wave)).continuousOn)
    (fun wave sample inside => observed_velocity_bound index order directions point wave ⟨sample, inside⟩)
    (fun wave sample inside => observed_rate_bound index order directions point wave ⟨sample, inside⟩) time
  rw [spatialWord_eq_sum]
  exact actual

theorem run_wordRate_summable (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    Summable fun wave => observeWord order directions wave point
      (receiptMomentumAction (run stackedShortCurrent index).receipt wave time.1) :=
  (decay_summable.mul_left (wordNorm order directions * rateBudget order index)).of_norm_bounded
    (fun wave => observed_rate_bound index order directions point wave time)

theorem run_wordRate_bound (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ‖wordRate index order directions point time.1‖ ≤
      (wordNorm order directions * rateBudget order index) * ∑' wave, decay wave := by
  have paid := (decay_summable.mul_left (wordNorm order directions * rateBudget order index)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun wave => observed_rate_bound index order directions point wave time)
  apply (norm_tsum_le_tsum_norm paid).trans
  have total := paid.tsum_le_tsum (fun wave => observed_rate_bound index order directions point wave time)
    (decay_summable.mul_left (wordNorm order directions * rateBudget order index))
  simpa only [tsum_mul_left] using total

theorem run_spatialWord_on_interval (index order : ℕ) (directions : Fin order → PhysicalSpace)
    (point : PhysicalSpace) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    spatialWord index order directions point time.1 =
      iteratedFDeriv ℝ order (spatialField (wholeBiotSavartVelocityState
        ((run stackedShortCurrent index).receipt.wholePath time))) point directions := by
  unfold spatialWord
  rw [projIcc_of_mem (run stackedShortCurrent index).receipt.requestedTimePos.le time.2]

end
end SaturationMonoid.NavierStokes.NativeFullOrderTime
