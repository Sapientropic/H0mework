import H0mework.NavierStokes.PhysicalReadout.Source
import H0mework.NavierStokes.FourWave.ReceiptDensity

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativePhysicalContinuous

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open NativePhysicalFourier NativePhysicalSource

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def scalarContinuous (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate) :
    C(Torus, ℂ) :=
  ∑' wave : IntegerWavevector, velocity wave coordinate • UnitAddTorus.mFourier wave

theorem scalarSummable (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    Summable fun wave : IntegerWavevector =>
      velocity wave coordinate • UnitAddTorus.mFourier wave := by
  apply Summable.of_norm
  simp only [norm_smul, UnitAddTorus.mFourier_norm, mul_one]
  apply paid.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro wave
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)

theorem scalarContinuous_toLp (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    (scalarContinuous velocity coordinate).toLp 2 volume ℂ = scalarField velocity coordinate := by
  have source := (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ).hasSum
    (scalarSummable velocity coordinate paid).hasSum
  have actual := UnitAddTorus.hasSum_mFourier_series_L2 (scalarField velocity coordinate)
  simp only [scalarField_fourier] at actual
  exact (source.congr_fun fun _ => by simp only [map_smul]).unique actual

theorem scalarContinuous_ae (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    scalarField velocity coordinate =ᵐ[volume] scalarContinuous velocity coordinate := by
  rw [← scalarContinuous_toLp velocity coordinate paid]
  exact ContinuousMap.coeFn_toLp volume _

def continuousField (velocity : ComplexVorticityHilbertState) : C(Torus, PhysicalSpace) where
  toFun point := WithLp.toLp 2 fun coordinate => (scalarContinuous velocity coordinate point).re
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Coordinate => ℝ)).comp
    apply continuous_pi
    intro coordinate
    exact Complex.continuous_re.comp (scalarContinuous velocity coordinate).continuous

theorem continuousField_ae (velocity : ComplexVorticityHilbertState)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    realField velocity =ᵐ[volume] continuousField velocity := by
  filter_upwards [realField_apply velocity,
    ae_all_iff.mpr (fun coordinate => scalarContinuous_ae velocity coordinate paid)]
    with point actual all
  rw [actual]
  apply PiLp.ext
  intro coordinate
  change (scalarField velocity coordinate point).re = _
  rw [all coordinate]
  rfl

theorem continuousField_fourier (velocity : ComplexVorticityHilbertState)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave)))
    (reality : ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory.FiniteStateFourierReality velocity)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (continuousField velocity point coordinate : ℂ)) wave =
      velocity wave coordinate := by
  rw [← realField_fourier velocity reality coordinate wave]
  apply integral_congr_ae
  filter_upwards [continuousField_ae velocity paid] with point actual
  rw [actual]

def realMode (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    C(Torus, PhysicalSpace) where
  toFun point := WithLp.toLp 2 fun coordinate =>
    (velocity wave coordinate * UnitAddTorus.mFourier wave point).re
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Coordinate => ℝ)).comp
    apply continuous_pi
    intro coordinate
    exact Complex.continuous_re.comp
      (continuous_const.mul (UnitAddTorus.mFourier wave).continuous)

theorem realMode_norm_le (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    ‖realMode velocity wave‖ ≤ Real.sqrt (complexCoordinateAmplitudeSq (velocity wave)) := by
  apply (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).mpr
  intro point
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg _), EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro coordinate _
  change ‖(velocity wave coordinate * UnitAddTorus.mFourier wave point).re‖ ^ 2 ≤
    Complex.normSq (velocity wave coordinate)
  rw [Complex.normSq_eq_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  have modeNorm : ‖UnitAddTorus.mFourier wave point‖ = 1 := by
    simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
      norm_prod, Circle.norm_coe, Finset.prod_const_one]
  simpa only [Real.norm_eq_abs, norm_mul, modeNorm, mul_one] using
    Complex.abs_re_le_norm (velocity wave coordinate * UnitAddTorus.mFourier wave point)

theorem realMode_summable (velocity : ComplexVorticityHilbertState)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    Summable (realMode velocity) :=
  (paid.of_nonneg_of_le (fun _ => norm_nonneg _) (realMode_norm_le velocity)).of_norm

theorem continuousField_eq_tsum (velocity : ComplexVorticityHilbertState)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    continuousField velocity = ∑' wave, realMode velocity wave := by
  ext point coordinate
  have vectorSum := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) coordinate).hasSum
    ((ContinuousMap.evalCLM ℝ point).hasSum (realMode_summable velocity paid).hasSum)
  have scalarSum := Complex.reCLM.hasSum
    ((ContinuousMap.evalCLM ℂ point).hasSum (scalarSummable velocity coordinate paid).hasSum)
  exact scalarSum.unique vectorSum

theorem continuousField_norm_le (velocity : ComplexVorticityHilbertState)
    (paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (velocity wave))) :
    ‖continuousField velocity‖ ≤ ∑' wave, Real.sqrt (complexCoordinateAmplitudeSq (velocity wave)) := by
  rw [continuousField_eq_tsum velocity paid]
  have normPaid := paid.of_nonneg_of_le (fun _ => norm_nonneg _) (realMode_norm_le velocity)
  exact (norm_tsum_le_tsum_norm normPaid).trans
    (normPaid.tsum_le_tsum (realMode_norm_le velocity) paid)

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {T : ℝ}

def continuousReceipt (receipt : WholeContinuousMildSerrinReceipt nu initial T)
    (time : Icc (0 : ℝ) T) : C(Torus, PhysicalSpace) :=
  continuousField (wholeBiotSavartVelocityState (receipt.wholePath time))

theorem receipt_paid (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ time ∂commonTimeMeasure T,
      Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq
        (wholeBiotSavartVelocityState (receipt.wholePath time) wave)) := by
  have pathAE := BoundedContinuousFunction.coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure T) ℂ receipt.wholePath
  rw [receipt.wholePath_toLp_eq_stateLimit] at pathAE
  filter_upwards [pathAE,
    wholePointwiseGradientDensity_ae_summable T receipt.stateLimit receipt.gradient_summable]
    with time same paid
  rw [same] at paid
  exact summable_wholeStateVelocityAmplitude (receipt.wholePath time) paid

theorem receipt_continuous_ae (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ time ∂commonTimeMeasure T,
      (receiptField receipt time =ᵐ[volume] continuousReceipt receipt time) ∧
      ‖continuousReceipt receipt time‖ ≤ wholeStateVelocityMajorant (receipt.wholePath time) := by
  filter_upwards [receipt_paid receipt] with time paid
  exact ⟨continuousField_ae _ paid, continuousField_norm_le _ paid⟩

theorem receipt_continuous_fourier (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ time ∂commonTimeMeasure T, ∀ coordinate wave,
      UnitAddTorus.mFourierCoeff
        (fun point => (continuousReceipt receipt time point coordinate : ℂ)) wave =
          biotSavartVelocityCoefficient wave (receipt.wholePath time wave) coordinate := by
  filter_upwards [receipt_paid receipt] with time paid coordinate wave
  exact continuousField_fourier _ paid
    (velocity_reality _ (receipt_reality receipt time)) coordinate wave

theorem receipt_Linfty (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    ∀ᵐ time ∂commonTimeMeasure T,
      MemLp (receiptField receipt time) ∞ (volume : Measure Torus) ∧
      eLpNorm (receiptField receipt time) ∞ (volume : Measure Torus) ≤
        ENNReal.ofReal (wholeStateVelocityMajorant (receipt.wholePath time)) := by
  filter_upwards [receipt_continuous_ae receipt] with time source
  have bound : ∀ᵐ point ∂(volume : Measure Torus),
      ‖receiptField receipt time point‖ ≤ wholeStateVelocityMajorant (receipt.wholePath time) := by
    filter_upwards [source.1] with point actual
    rw [actual]
    exact ((continuousReceipt receipt time).norm_coe_le_norm point).trans source.2
  exact ⟨memLp_top_of_bound (Lp.aestronglyMeasurable _) _ bound,
    eLpNormEssSup_le_of_ae_bound bound⟩

theorem receipt_majorant_integrable (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    Integrable (fun time => wholeStateVelocityMajorant (receipt.wholePath time) ^ 2)
      (commonTimeMeasure T) :=
  HeatQuartetBudget.velocitySquare_integrable receipt

theorem sourceMode_continuous (wave : IntegerWavevector) :
    Continuous (fun state : ComplexVorticityHilbertState =>
      realMode (wholeBiotSavartVelocityState state) wave) := by
  apply ContinuousMap.continuous_of_continuous_uncurry _
  apply (PiLp.continuous_toLp 2 (fun _ : Coordinate => ℝ)).comp
  apply continuous_pi
  intro coordinate
  apply Complex.continuous_re.comp
  apply Continuous.mul
  · exact ((continuous_apply coordinate).comp
      (ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.biotSavartVelocityCLM wave).continuous).comp
        (((lp.evalCLM ℂ _ 2 wave).continuous).comp continuous_fst)
  · exact (UnitAddTorus.mFourier wave).continuous.comp continuous_snd

theorem receipt_continuous_measurable (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    AEStronglyMeasurable (continuousReceipt receipt) (commonTimeMeasure T) := by
  have series : AEStronglyMeasurable
      (fun time => ∑' wave, realMode (wholeBiotSavartVelocityState (receipt.wholePath time)) wave)
      (commonTimeMeasure T) := by
    apply AEStronglyMeasurable.tsum
    intro wave
    exact ((sourceMode_continuous wave).comp receipt.wholePath.continuous).aestronglyMeasurable
  apply series.congr
  filter_upwards [receipt_paid receipt] with time paid
  exact (continuousField_eq_tsum _ paid).symm

theorem receipt_continuous_sq_integrable (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    Integrable (fun time => ‖continuousReceipt receipt time‖ ^ 2) (commonTimeMeasure T) := by
  apply (receipt_majorant_integrable receipt).mono_nonneg
    ((receipt_continuous_measurable receipt).norm.pow 2)
  · exact Eventually.of_forall fun _ => sq_nonneg _
  · filter_upwards [receipt_continuous_ae receipt] with time source
    exact (sq_le_sq₀ (norm_nonneg _) (wholeStateVelocityMajorant_nonneg _)).mpr source.2

theorem receipt_continuous_memLp (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    MemLp (continuousReceipt receipt) 2 (commonTimeMeasure T) :=
  (memLp_two_iff_integrable_sq_norm (receipt_continuous_measurable receipt)).mpr
    (receipt_continuous_sq_integrable receipt)

theorem receipt_continuous_integral_le (receipt : WholeContinuousMildSerrinReceipt nu initial T) :
    (∫ time, ‖continuousReceipt receipt time‖ ^ 2 ∂commonTimeMeasure T) ≤
      3 * (biotSavartSerrinConstant * ∑' wave, integerWaveCriticalKernel wave) *
        wholeSpaceTimeVorticityGradientMass T receipt.stateLimit := by
  have bound : (∫ time, ‖continuousReceipt receipt time‖ ^ 2 ∂commonTimeMeasure T) ≤
      ∫ time, wholeStateVelocityMajorant (receipt.wholePath time) ^ 2 ∂commonTimeMeasure T := by
    apply integral_mono_ae (receipt_continuous_sq_integrable receipt)
      (receipt_majorant_integrable receipt)
    filter_upwards [receipt_continuous_ae receipt] with time source
    exact (sq_le_sq₀ (norm_nonneg _) (wholeStateVelocityMajorant_nonneg _)).mpr source.2
  apply bound.trans
  have same : (∫ time, wholeStateVelocityMajorant (receipt.wholePath time) ^ 2 ∂commonTimeMeasure T) =
      ∫ time, wholeStateVelocityMajorant (receipt.stateLimit time) ^ 2 ∂commonTimeMeasure T := by
    apply integral_congr_ae
    have pathAE := BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞)) (μ := commonTimeMeasure T) ℂ receipt.wholePath
    rw [receipt.wholePath_toLp_eq_stateLimit] at pathAE
    filter_upwards [pathAE] with time actual
    rw [actual]
  rw [same]
  exact wholeVelocityMajorantSq_integral_le T receipt.stateLimit receipt.gradient_summable

end
end SaturationMonoid.NavierStokes.NativePhysicalContinuous
