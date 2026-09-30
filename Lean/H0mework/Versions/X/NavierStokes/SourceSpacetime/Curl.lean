import H0mework.Versions.X.NavierStokes.SourceSpacetime.Time
import H0mework.Versions.X.NavierStokes.SourceHeat.PairingAverage
import H0mework.Versions.X.NavierStokes.StressWholeH1.Cancellation
import H0mework.Versions.X.NavierStokes.PhysicalJets.ChartVorticity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeViewPhysicalCurl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeForwardWindowSource
open NativeFullOrderSynthesis NativeFullOrderAction NativeWindowSpacetimeFourier NativeViewPhysicalTime
open NativeWholeResolvent NativeWholeH1Mixed
noncomputable section
variable {nu : Viscosity}

theorem window_transverse (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) :
    WholeStateTransverse (wholeVelocity (NativeForwardWindowSource.source seed time).fst) := by
  intro wave
  let read : FullSpace →L[ℝ] ℂ := (NativeCompleteVelocityCurl.dotCLM wave).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
      (wholeVelocityCLM.comp NativeForwardWindowPairingReadout.meanRead))
  have original := NativeForwardWindowPairingReadout.linear_integral read seed time
  change read (NativeForwardWindowSource.source seed time) = _
  rw [original]
  apply integral_eq_zero_of_ae
  filter_upwards with shift
  by_cases zero : kernel shift = 0
  · simp only [zero, zero_smul, Pi.zero_apply]
  · have actual := NativeCompleteVelocityCurl.source_transverse seed (time - shift)
      (by linarith [kernel_support shift zero]) wave
    change kernel shift • NativeCompleteVelocityCurl.dotCLM wave
      (wholeVelocity (NativeUnifiedCompleteSource.source seed (time - shift)).fst wave) = 0
    rw [NativeCompleteVelocityCurl.dotCLM_apply, actual, smul_zero]

theorem source_transverse (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) (valid : -1 ≤ time) :
    WholeRestartVelocityEndpointTransverse (NativeWindowHeatEvolution.source seed lag time).fst := by
  intro wave
  have original := window_transverse seed time valid wave.1
  have heated : complexWavevector wave.1 ⬝ᵥ
      wholeVelocity (NativeWindowHeatEvolution.source seed lag time).fst wave.1 = 0 := by
    change NativeCompleteVelocityCurl.dotCLM wave.1
      (wholeVelocity (NativeUnifiedHeatAction.heatCLM nu lag (NativeForwardWindowSource.source seed time).fst) wave.1) = 0
    rw [NativeCompleteHeatTransport.velocity_heat, map_smul, NativeCompleteVelocityCurl.dotCLM_apply, original, smul_zero]
  have same : wholeVelocity (NativeWindowHeatEvolution.source seed lag time).fst wave.1 =
      fun coordinate => (NativeWindowHeatEvolution.source seed lag time).fst wave coordinate := by
    funext coordinate
    exact wholeVelocity_nonzero _ wave coordinate
  exact (congrArg (fun row => complexWavevector wave.1 ⬝ᵥ row) same).symm.trans heated

def sourcePhysical (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) (valid : -1 ≤ time) : wholePhysical :=
  ⟨(NativeWindowHeatEvolution.source seed lag time).fst,
    source_transverse seed lag time valid,
    NativeHeatPairingAverage.heat_mean_reality nu lag (NativeForwardWindowSource.source seed time)
      (NativeForwardWindowPairing.data seed time) rfl rfl⟩

theorem sourcePhysical_H1 (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 ≤ time) : H1 (sourcePhysical seed lag time valid) := by
  have original := velocity_gradient_summable seed lag positive 0 time
  change Summable (fun wave => integerWaveNormSq wave *
    NativeMovingCriticalProduct.amplitude (wholeVelocity (NativeWindowHeatEvolution.source seed lag time).fst) wave ^ 2)
  simp only [NativeMovingCriticalProduct.amplitude,
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.euclideanCoordinateRow_norm_sq]
  simpa only [
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.euclideanCoordinateRow_norm_sq,
    NativeWindowHeatEvolution.velocityJet, NativeWindowHeatEvolution.jet_zero] using! original

def vorticityJet (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  wholeVelocityCurlState (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order time))
    (velocity_gradient_summable seed lag positive order time)

theorem vorticity_row (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) (wave : IntegerWavevector) :
    vorticityJet seed lag positive order time wave =
      fourierCurlCoefficient wave (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order time) wave) := rfl

theorem vorticity_square_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (word order : ℕ) (time : ℝ) :
    Summable (fun wave => frequencySize wave ^ (2 * order) *
      complexCoordinateAmplitudeSq (vorticityJet seed lag positive word time wave)) := by
  have paid := (NativeHeatSpatialSynthesis.velocity_square_summable nu lag positive
    (NativeForwardWindowJets.jet seed word time).fst (order + 1)).mul_left ((2 * Real.pi) ^ 2)
  apply paid.of_nonneg_of_le (fun wave => mul_nonneg (pow_nonneg (frequencySize_nonneg wave) _)
    (complexCoordinateAmplitudeSq_nonneg _))
  intro wave
  have curl := NativeFullOrderActionMoments.curl_amplitude_le wave
    (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag word time) wave)
  have frequency := mul_le_mul_of_nonneg_left (normSq_le_frequencySize_sq wave) (sq_nonneg (2 * Real.pi))
  have amplitude := curl.trans (mul_le_mul_of_nonneg_right frequency (complexCoordinateAmplitudeSq_nonneg _))
  rw [vorticity_row]
  apply (mul_le_mul_of_nonneg_left amplitude (pow_nonneg (frequencySize_nonneg wave) _)).trans_eq
  change _ = (2 * Real.pi) ^ 2 * (frequencySize wave ^ (2 * (order + 1)) *
    complexCoordinateAmplitudeSq (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag word time) wave))
  rw [Nat.mul_add, Nat.mul_one, pow_add]
  ring

theorem vorticity_moments (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (word order : ℕ) (time : ℝ) :
    Summable (fun wave => frequencySize wave ^ order * NativeFullOrderAction.amplitude
      (vorticityJet seed lag positive word time) wave) :=
  summable_moment_of_square _ order (vorticity_square_summable seed lag positive word (order + 2) time)

def vorticityWord (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (pair : Spacetime) : PhysicalSpace :=
  spatialField (vorticityJet seed lag positive order pair.1) pair.2

theorem vorticityWord_curl (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (pair : Spacetime) :
    vorticityWord seed lag positive order pair = NativeTimeChartVorticityReadout.spatialCurl
      (fun space => velocityWord seed lag order (pair.1, space)) pair.2 := by
  have velocity : ∀ spatial, Summable (fun wave => frequencySize wave ^ spatial *
      NativeFullOrderAction.amplitude (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order pair.1)) wave) :=
    fun spatial => summable_moment_of_square _ spatial (NativeHeatSpatialSynthesis.velocity_square_summable
      nu lag positive (NativeForwardWindowJets.jet seed order pair.1).fst (spatial + 2))
  have vorticity : Summable (NativeFullOrderAction.amplitude (vorticityJet seed lag positive order pair.1)) := by
    simpa only [pow_zero, one_mul] using vorticity_moments seed lag positive order 0 pair.1
  exact (NativeTimeChartVorticityReadout.spatialCurl_of_fourier _ _ velocity vorticity
    (fun wave => (vorticity_row seed lag positive order pair.1 wave).symm) pair.2).symm

def spatialDerivativeRead (direction output : Coordinate) :
    (Spacetime →L[ℝ] PhysicalSpace) →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) output).comp
    (ContinuousLinearMap.apply ℝ PhysicalSpace (0, EuclideanSpace.single direction 1))

def jointCurlRead : (Spacetime →L[ℝ] PhysicalSpace) →L[ℝ] PhysicalSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![spatialDerivativeRead 1 2 - spatialDerivativeRead 2 1,
      spatialDerivativeRead 2 0 - spatialDerivativeRead 0 2, spatialDerivativeRead 0 1 - spatialDerivativeRead 1 0])

theorem jointCurlRead_apply (derivative : Spacetime →L[ℝ] PhysicalSpace) :
    jointCurlRead derivative = WithLp.toLp 2 ![
      derivative (0, EuclideanSpace.single 1 1) 2 - derivative (0, EuclideanSpace.single 2 1) 1,
      derivative (0, EuclideanSpace.single 2 1) 0 - derivative (0, EuclideanSpace.single 0 1) 2,
      derivative (0, EuclideanSpace.single 0 1) 1 - derivative (0, EuclideanSpace.single 1 1) 0] := by
  ext coordinate
  fin_cases coordinate <;> rfl

theorem vorticityWord_derivative (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (pair : Spacetime) :
    vorticityWord seed lag positive order pair = jointCurlRead (fderiv ℝ (velocityWord seed lag order) pair) := by
  have curve : HasFDerivAt (fun space : PhysicalSpace => (pair.1, space))
      ((0 : PhysicalSpace →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ PhysicalSpace)) pair.2 :=
    (hasFDerivAt_const pair.1 pair.2).prodMk (hasFDerivAt_id pair.2)
  have generated := ((velocityWord_smooth seed lag positive order).differentiable (by simp) pair).hasFDerivAt.comp pair.2 curve
  have written : fderiv ℝ (fun space => velocityWord seed lag order (pair.1, space)) pair.2 =
      (fderiv ℝ (velocityWord seed lag order) pair).comp
        ((0 : PhysicalSpace →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ PhysicalSpace)) := generated.fderiv
  rw [vorticityWord_curl, NativeTimeChartVorticityReadout.spatialCurl, written, jointCurlRead_apply]
  rfl

theorem vorticityWord_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) : ContDiff ℝ ∞ (vorticityWord seed lag positive order) := by
  have same : vorticityWord seed lag positive order =
      fun pair => jointCurlRead (fderiv ℝ (velocityWord seed lag order) pair) :=
    funext (vorticityWord_derivative seed lag positive order)
  rw [same]
  exact jointCurlRead.contDiff.comp (contDiff_infty_iff_fderiv.mp (velocityWord_smooth seed lag positive order)).2

theorem vorticityWord_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (word order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (vorticityWord seed lag positive word)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (vorticityWord seed lag positive word)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (vorticityWord_smooth seed lag positive word) order exponent compact

end
end SaturationMonoid.NavierStokes.NativeViewPhysicalCurl
