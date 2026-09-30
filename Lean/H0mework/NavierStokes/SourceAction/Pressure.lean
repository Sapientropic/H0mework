import H0mework.NavierStokes.SourceAction.Flux
import H0mework.NavierStokes.SourceReadout.Action

set_option autoImplicit false
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace SaturationMonoid.NavierStokes.NativePressureFullOrder

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeStressSource NativeStressCurlAlgebra
open NativeFullOrderAction NativeFullOrderNext NativeFullOrderFlux NativeFullOrderSynthesis
open NativePhysicalFourier NativePhysicalContinuous NativePhysicalSource

noncomputable section

theorem pressure_contraction_normSq_le (wave : IntegerWavevector) (tensor : NativeFluidStressCoefficient) :
    Complex.normSq (stressPressureCoefficient wave tensor) ≤
      ∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (tensor output input) := by
  by_cases atZero : wave = 0
  · simp only [stressPressureCoefficient, if_pos atZero, map_zero]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  · have positive := integerWaveNormSq_pos atZero
    let row : ComplexCoordinateVector := fun output => complexWavevector wave ⬝ᵥ tensor output
    have inside : complexCoordinateAmplitudeSq row ≤
        integerWaveNormSq wave * ∑ output : Coordinate, ∑ input : Coordinate, Complex.normSq (tensor output input) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun output _ => complexWavevector_dot_normSq_le wave (tensor output)
    have twice := (complexWavevector_dot_normSq_le wave row).trans
      (mul_le_mul_of_nonneg_left inside positive.le)
    rw [stressPressureCoefficient, if_neg atZero, Complex.normSq_div, Complex.normSq_ofReal]
    apply (div_le_iff₀ (mul_pos positive positive)).mpr
    change Complex.normSq (complexWavevector wave ⬝ᵥ row) ≤ _
    convert! twice using 1
    ring

def pressureMomentDensity (order : ℕ) (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) : ℝ :=
  (frequencySize wave ^ order) ^ 2 * Complex.normSq (sourcePressure state wave)

theorem pressureMomentDensity_nonnegative (order : ℕ) (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    0 ≤ pressureMomentDensity order state wave := mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)

theorem pressureMomentDensity_le_flux (order : ℕ) (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    pressureMomentDensity order state wave ≤
      ∑ output : Coordinate, ∑ input : Coordinate,
        fluxMomentDensity order (wholeBiotSavartVelocityState state) output input wave := by
  have weighted := mul_le_mul_of_nonneg_left
    (pressure_contraction_normSq_le wave (quadraticFlux (wholeBiotSavartVelocityState state) wave))
    (sq_nonneg (frequencySize wave ^ order))
  simpa only [pressureMomentDensity, sourcePressure, fluxMomentDensity, Finset.mul_sum] using weighted

def sourcePressureBudget (order index : ℕ) : ℝ := 9 * sourceFluxBudget order index

theorem run_receipt_pressure_control (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    Summable (pressureMomentDensity order ((run stackedShortCurrent index).receipt.wholePath time)) ∧
      (∑' wave, pressureMomentDensity order ((run stackedShortCurrent index).receipt.wholePath time) wave) ≤
        sourcePressureBudget order index := by
  let state := (run stackedShortCurrent index).receipt.wholePath time
  have paid output input := run_receipt_flux_control order index time output input
  have totalPaid : Summable fun wave => ∑ output : Coordinate, ∑ input : Coordinate,
      fluxMomentDensity order (wholeBiotSavartVelocityState state) output input wave :=
    summable_sum fun output _ => summable_sum fun input _ => (paid output input).1
  have generated := totalPaid.of_nonneg_of_le (pressureMomentDensity_nonnegative order state)
    (pressureMomentDensity_le_flux order state)
  refine ⟨generated, ?_⟩
  have boundAll := generated.tsum_le_tsum (pressureMomentDensity_le_flux order state) totalPaid
  rw [Summable.tsum_finsetSum] at boundAll
  · apply boundAll.trans
    have each (output : Coordinate) :
        (∑' wave, ∑ input : Coordinate, fluxMomentDensity order (wholeBiotSavartVelocityState state) output input wave) ≤
          3 * sourceFluxBudget order index := by
      rw [Summable.tsum_finsetSum (fun input _ => (paid output input).1)]
      have finite := Finset.sum_le_sum fun input (_ : input ∈ (Finset.univ : Finset Coordinate)) => (paid output input).2
      simpa using finite
    have finite := Finset.sum_le_sum fun output (_ : output ∈ (Finset.univ : Finset Coordinate)) => each output
    apply finite.trans_eq
    norm_num [sourcePressureBudget]
    ring
  · intro output _
    exact summable_sum fun input _ => (paid output input).1

theorem quadraticFlux_reality (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) (wave : IntegerWavevector) (output input : Coordinate) :
    quadraticFlux velocity (waveNeg wave) output input = conj (quadraticFlux velocity wave output input) := by
  have incidence (first : IntegerWavevector) :
      waveNeg wave - waveNeg first = waveNeg (wave - first) := by
    ext coordinate
    simp [waveNeg]
    abel
  unfold quadraticFlux
  rw [map_neg, Complex.conj_tsum]
  apply congrArg Neg.neg
  calc
    (∑' first, velocity first input * velocity (waveNeg wave - first) output) =
        ∑' first, velocity (waveNeg first) input * velocity (waveNeg wave - waveNeg first) output :=
      (integerWaveNegEquiv.tsum_eq (fun first => velocity first input * velocity (waveNeg wave - first) output)).symm
    _ = _ := by
      apply tsum_congr
      intro first
      rw [incidence, reality first, reality (wave - first)]
      simp only [vectorConj, map_mul]
      rfl

theorem stressPressure_reality (wave : IntegerWavevector) (tensor : NativeFluidStressCoefficient) :
    stressPressureCoefficient (waveNeg wave) (fun output input => conj (tensor output input)) =
      conj (stressPressureCoefficient wave tensor) := by
  by_cases atZero : wave = 0
  · subst wave
    simp [stressPressureCoefficient, waveNeg]
  · have negativeNe : waveNeg wave ≠ 0 := by
      change -wave ≠ 0
      exact neg_ne_zero.mpr atZero
    simp only [stressPressureCoefficient, if_neg atZero, if_neg negativeNe, complexWavevector_waveNeg]
    simp only [dotProduct, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]
    simp [integerWaveNormSq, waveNeg, complexWavevector, map_div₀, map_sum, map_mul]

theorem sourcePressure_reality (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) (wave : IntegerWavevector) :
    sourcePressure state (waveNeg wave) = conj (sourcePressure state wave) := by
  have tensorEq : quadraticFlux (wholeBiotSavartVelocityState state) (waveNeg wave) =
      fun output input => conj (quadraticFlux (wholeBiotSavartVelocityState state) wave output input) := by
    funext output input
    exact quadraticFlux_reality _ (velocity_reality state reality) wave output input
  rw [sourcePressure, tensorEq, stressPressure_reality]
  rfl

def pressureState (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ComplexVorticityHilbertState :=
  ⟨fun wave => Pi.single (0 : Coordinate)
    (sourcePressure ((run stackedShortCurrent index).receipt.wholePath time) wave), by
      apply memℓp_gen
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      have paid := (run_receipt_pressure_control 0 index time).1
      change Summable (fun wave => (frequencySize wave ^ 0) ^ 2 *
        Complex.normSq (sourcePressure ((run stackedShortCurrent index).receipt.wholePath time) wave)) at paid
      simpa only [pow_zero, one_pow, one_mul, Pi.norm_single, Complex.normSq_eq_norm_sq] using paid⟩

theorem pressureState_apply (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    pressureState index time wave coordinate =
      (Pi.single (0 : Coordinate) (sourcePressure ((run stackedShortCurrent index).receipt.wholePath time) wave) :
        ComplexCoordinateVector) coordinate := rfl

theorem pressureState_moment_eq (index order : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    (fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (pressureState index time wave)) =
      pressureMomentDensity order ((run stackedShortCurrent index).receipt.wholePath time) := by
  funext wave
  simp only [complexCoordinateAmplitudeSq, pressureState_apply, Pi.single_apply]
  simp only [apply_ite Complex.normSq, map_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [pressureMomentDensity, ← pow_mul, Nat.mul_comm order 2]

theorem pressureState_moments (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (order : ℕ) :
    Summable (fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (pressureState index time wave)) := by
  rw [pressureState_moment_eq]
  exact (run_receipt_pressure_control order index time).1

theorem pressureState_amplitude_summable (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq (pressureState index time wave)) := by
  simpa only [pow_zero, one_mul, amplitude, vorticityRowAmplitude,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
    summable_moment_of_square (pressureState index time) 0 (pressureState_moments index time 2)

theorem pressureState_reality (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    FiniteStateFourierReality (pressureState index time) := by
  intro wave
  funext coordinate
  simp only [pressureState_apply, vectorConj,
    sourcePressure_reality _ (receipt_reality _ time)]
  by_cases coordinateZero : coordinate = 0
  · subst coordinate
    simp
  · simp [coordinateZero]

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pressureL2 (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) : ScalarField :=
  scalarField (pressureState index time) 0

theorem pressureL2_fourier (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (pressureL2 index time) wave =
      sourcePressure ((run stackedShortCurrent index).receipt.wholePath time) wave := by
  rw [pressureL2, scalarField_fourier, pressureState_apply]
  simp

def pressureContinuous (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) : C(Torus, ℝ) where
  toFun point := continuousField (pressureState index time) point 0
  continuous_toFun := (EuclideanSpace.proj (0 : Coordinate)).continuous.comp
    (continuousField (pressureState index time)).continuous

theorem pressureContinuous_fourier (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => (pressureContinuous index time point : ℂ)) wave =
      sourcePressure ((run stackedShortCurrent index).receipt.wholePath time) wave := by
  change UnitAddTorus.mFourierCoeff
    (fun point => (continuousField (pressureState index time) point 0 : ℂ)) wave = _
  rw [continuousField_fourier (pressureState index time) (pressureState_amplitude_summable index time)
    (pressureState_reality index time) 0 wave, pressureState_apply]
  simp

theorem pressureContinuous_ae_eq_original (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    pressureL2 index time =ᵐ[volume] fun point => (pressureContinuous index time point : ℂ) := by
  filter_upwards [realValue_recovers_complex (pressureState index time) (pressureState_reality index time),
    realField_apply (pressureState index time),
    continuousField_ae (pressureState index time) (pressureState_amplitude_summable index time)]
    with point real original continuous
  change scalarField (pressureState index time) 0 point =
    (continuousField (pressureState index time) point 0 : ℂ)
  rw [← real 0, ← continuous, original]

theorem run_pressure_momentum_action (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (wave : IntegerWavevector) (nonzero : wave ≠ 0) :
    let state := (run stackedShortCurrent index).receipt.wholePath time
    biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt butterflyGainViscosity.coeff state wave) =
      nativeFluidStressDivergenceCoefficient (quadraticFlux (wholeBiotSavartVelocityState state)) wave -
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
          UnitAddTorus.mFourierCoeff (fun point => (pressureContinuous index time point : ℂ)) wave) • complexWavevector wave -
        (butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave) • wholeBiotSavartVelocityState state wave := by
  dsimp only
  rw [pressureContinuous_fourier]
  exact source_momentum_action _ _ ((run stackedShortCurrent index).receipt.wholePath_zero_row time)
    (wholePath_transverse _ time) wave nonzero

def pressureField (index : ℕ) (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) : PhysicalSpace → ℝ :=
  fun point => pressureContinuous index time (circlePoint point)

theorem pressureField_eq_original_modes (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (point : PhysicalSpace) :
    pressureField index time point = ∑' wave,
      (sourcePressure ((run stackedShortCurrent index).receipt.wholePath time) wave *
        UnitAddTorus.mFourier wave (circlePoint point)).re := by
  have original := Complex.reCLM.hasSum
    ((ContinuousMap.evalCLM ℂ (circlePoint point)).hasSum
      (scalarSummable (pressureState index time) 0 (pressureState_amplitude_summable index time)).hasSum)
  change HasSum (fun wave =>
    (pressureState index time wave 0 * UnitAddTorus.mFourier wave (circlePoint point)).re)
      (pressureField index time point) at original
  simpa only [pressureState_apply, Pi.single_eq_same] using original.tsum_eq.symm

def pressureJetBudget (order index : ℕ) : ℝ :=
  (2 * Real.pi) ^ order * ((sourcePressureBudget (order + 2) index + ∑' wave, decay wave) / 2)

private def scalarProjection : PhysicalSpace →L[ℝ] ℝ := EuclideanSpace.proj 0

private theorem scalarProjection_norm : ‖scalarProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro point
  change ‖point (0 : Coordinate)‖ ≤ 1 * ‖point‖
  simpa only [one_mul] using PiLp.norm_apply_le point (0 : Coordinate)

theorem pressureField_spatial_control (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (pressureField index time) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order (pressureField index time) point‖ ≤ pressureJetBudget order index := by
  have source := spatialField_smooth_of_square (pressureState index time) (pressureState_moments index time)
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (scalarProjection ∘ spatialField (pressureState index time)) ∧ _
  refine ⟨scalarProjection.contDiff.comp source, ?_⟩
  intro order point
  change ‖iteratedFDeriv ℝ order (scalarProjection ∘ spatialField (pressureState index time)) point‖ ≤ _
  rw [scalarProjection.iteratedFDeriv_comp_left source.contDiffAt
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  apply (scalarProjection.norm_compContinuousMultilinearMap_le _).trans
  apply (mul_le_mul_of_nonneg_right scalarProjection_norm (norm_nonneg _)).trans
  rw [one_mul]
  apply (spatialField_bound_of_square (pressureState index time) (pressureState_moments index time) order point).trans
  unfold pressureJetBudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply add_le_add _ le_rfl
  rw [pressureState_moment_eq]
  exact (run_receipt_pressure_control (order + 2) index time).2

theorem pressureField_spatial_Lp (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) (order : ℕ)
    (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order (pressureField index time)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (pressureField index time)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal (pressureJetBudget order index) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have source := pressureField_spatial_control index time
  have continuous : Continuous (iteratedFDeriv ℝ order (pressureField index time)) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) source.1
  have bound : ∀ᵐ point ∂volume.restrict domain,
      ‖iteratedFDeriv ℝ order (pressureField index time) point‖ ≤ pressureJetBudget order index :=
    Eventually.of_forall (source.2 order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ bound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) bound⟩

end
end SaturationMonoid.NavierStokes.NativePressureFullOrder
