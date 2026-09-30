import H0mework.NavierStokes.WindowPhysics.SpacetimeFourier
import H0mework.NavierStokes.WindowPhysics.HeatSpatialSynthesis
import H0mework.NavierStokes.WindowPhysics.HeatEvolution

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowSpacetimeVelocity

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier

noncomputable section

variable {nu : Viscosity}

def read (wave : IntegerWavevector) (coordinate : Coordinate) : WholeRestartVelocityEndpointState →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj coordinate).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp wholeVelocityCLM)

def coefficient (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (coordinate : Coordinate)
    (order : ℕ) (wave : IntegerWavevector) (time : ℝ) : ℂ :=
  wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag order time) wave coordinate

theorem coefficient_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (coordinate : Coordinate)
    (order : ℕ) (wave : IntegerWavevector) (time : ℝ) :
    HasDerivAt (coefficient seed lag coordinate order wave)
      (coefficient seed lag coordinate (order + 1) wave time) time :=
  (read wave coordinate).hasFDerivAt.comp_hasDerivAt time
    (NativeWindowHeatEvolution.velocityJet_hasDerivAt seed lag order time)

def coefficientBudget (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (rank order : ℕ) : ℝ :=
  NativeHeatSpatialMultiplier.budget nu lag (order + 4) * NativeForwardWindowJets.budget seed rank

theorem coefficient_decay (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (rank order : ℕ) (wave : IntegerWavevector) (time : ℝ) :
    frequencySize wave ^ order * ‖coefficient seed lag coordinate rank wave time‖ ≤
      coefficientBudget seed lag rank order * decay wave := by
  have nonnegative := (norm_nonneg (NativeForwardWindowJets.jet seed rank time)).trans
    (NativeForwardWindowJets.jet_bound seed rank time)
  have rawBound : ‖wholeVelocity (NativeForwardWindowJets.jet seed rank time).fst wave coordinate‖ ≤
      NativeForwardWindowJets.budget seed rank :=
    (norm_le_pi_norm _ coordinate).trans
      ((lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ wave).trans
        ((wholeVelocity_norm_le _).trans ((WithLp.norm_fst_le _ _).trans (NativeForwardWindowJets.jet_bound seed rank time))))
  change frequencySize wave ^ order *
    ‖wholeVelocity (NativeUnifiedHeatAction.heatCLM nu lag (NativeForwardWindowJets.jet seed rank time).fst) wave coordinate‖ ≤ _
  rw [NativeCompleteHeatTransport.velocity_heat, Pi.smul_apply]
  simpa only [Nat.add_zero, pow_zero, one_mul, coefficientBudget] using
    heated_coefficient_bound nu lag positive 0 order wave
      (wholeVelocity (NativeForwardWindowJets.jet seed rank time).fst wave coordinate)
      (NativeForwardWindowJets.budget seed rank) nonnegative (by simpa using rawBound)

theorem scalar_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) :
    ContDiff ℝ ∞ (scalarField (coefficient seed lag coordinate)) :=
  scalarField_smooth _ (coefficient_hasDerivAt seed lag coordinate) (coefficientBudget seed lag)
    (coefficient_decay seed lag positive coordinate)

def jointField (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) : PhysicalSpace :=
  spatialField (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag 0 pair.1)) pair.2

theorem jointField_source (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) :
    jointField seed lag pair = spatialField (wholeVelocity (NativeWindowHeatEvolution.source seed lag pair.1).fst) pair.2 := by
  unfold jointField NativeWindowHeatEvolution.velocityJet
  rw [NativeWindowHeatEvolution.jet_zero]

theorem jointField_coordinate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (coordinate : Coordinate) (pair : Spacetime) :
    jointField seed lag pair coordinate = (scalarField (coefficient seed lag coordinate) pair).re := by
  have paid : Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag 0 pair.1) wave)) := by
    change Summable fun wave => Real.sqrt (complexCoordinateAmplitudeSq
      (wholeVelocity (NativeUnifiedHeatAction.heatCLM nu lag (NativeForwardWindowJets.jet seed 0 pair.1).fst) wave))
    have moments := NativeHeatSpatialSynthesis.velocity_square_summable nu lag positive
      (NativeForwardWindowJets.jet seed 0 pair.1).fst 2
    simpa only [pow_zero, one_mul, amplitude, vorticityRowAmplitude,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using
        summable_moment_of_square _ 0 moments
  have written := (ContinuousMap.evalCLM ℂ (circlePoint pair.2)).hasSum
    (NativePhysicalContinuous.scalarSummable
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag 0 pair.1)) coordinate paid).hasSum
  change HasSum (fun wave => scalarMode (coefficient seed lag coordinate) wave pair)
    (NativePhysicalContinuous.scalarContinuous
      (wholeVelocity (NativeWindowHeatEvolution.velocityJet seed lag 0 pair.1)) coordinate (circlePoint pair.2)) at written
  exact (congrArg Complex.re written.tsum_eq).symm

theorem jointField_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag) :
    ContDiff ℝ ∞ (jointField seed lag) := by
  have same : jointField seed lag = fun pair => WithLp.toLp 2
      (fun coordinate : Coordinate => (scalarField (coefficient seed lag coordinate) pair).re) := by
    funext pair
    apply PiLp.ext
    exact fun coordinate => jointField_coordinate seed lag positive coordinate pair
  rw [same]
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro coordinate
  exact Complex.reCLM.contDiff.comp (scalar_smooth seed lag positive coordinate)

theorem jointField_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (jointField seed lag)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (jointField seed lag)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (jointField_smooth seed lag positive) order exponent compact

theorem jointField_next (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : PhysicalSpace) :
    jointField seed lag (response.2.clockAdvance + time, space) = jointField response.1 lag (time, space) := by
  rw [jointField_source, jointField_source]
  change spatialField (wholeVelocity (NativeWindowHeatEvolution.source seed lag (response.2.clockAdvance + time)).fst) space = _
  rw [NativeWindowHeatEvolution.source_next seed lag response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowSpacetimeVelocity
