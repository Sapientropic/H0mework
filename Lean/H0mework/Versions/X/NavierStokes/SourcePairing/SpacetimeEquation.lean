import H0mework.Versions.X.NavierStokes.SourceSpacetime.Curl
import H0mework.Versions.X.NavierStokes.SourcePairing.NativeActionLineSpatialOperators

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeViewPhysicalEquation
open Set Filter MeasureTheory
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineCanonicalCauchyState
open PhysicsCore.StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open PhysicsCore.Stage9CU
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeFullOrderSynthesis NativeWindowSpacetimeFourier NativeViewPhysicalTime NativeViewPhysicalCurl
noncomputable section
variable {nu : Viscosity}

def momentumField (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) : PhysicalSpace :=
  WithLp.toLp 2 (fun coordinate => (∑' wave,
    NativeCompleteAction.momentum nu (NativeWindowHeatEvolution.source seed lag pair.1) wave coordinate *
      NativeFullOrderSynthesis.monomial wave pair.2).re)

theorem momentum_summable (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (space : PhysicalSpace) (coordinate : Coordinate) :
    Summable (fun wave => NativeCompleteAction.momentum nu (NativeWindowHeatEvolution.source seed lag time) wave coordinate *
      NativeFullOrderSynthesis.monomial wave space) := by
  simpa only [NativeWindowSpacetimeVelocity.coefficient, momentum_row seed lag time valid] using
    scalarWord_summable seed lag positive coordinate 1 (time, space)

theorem momentumField_eq (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (space : PhysicalSpace) :
    momentumField seed lag (time, space) = velocityWord seed lag 1 (time, space) := by
  apply PiLp.ext
  intro coordinate
  rw [velocityWord_coordinate seed lag positive coordinate 1]
  simp only [momentumField, scalarWord, NativeWindowSpacetimeVelocity.coefficient,
    momentum_row seed lag time valid]

theorem physical_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (space : PhysicalSpace) :
    HasDerivAt (fun sample => NativeWindowSpacetimeVelocity.jointField seed lag (sample, space))
      (momentumField seed lag (time, space)) time := by
  rw [momentumField_eq seed lag positive time valid space]
  exact velocityWord_hasDerivAt seed lag positive 0 time space

def field (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (point : BasePoint) : PhysicalSpace :=
  velocityWord seed lag order (canonicalTimeProjection point, canonicalSpatialProjection point)

theorem field_slice (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ)
    (time : ℝ) (space : PhysicalSpace) :
    field seed lag order (canonicalCauchySlicePoint time space) = velocityWord seed lag order (time, space) := by
  simp only [field, canonicalTimeProjection_slice, canonicalSpatialProjection_slice]

theorem coordinate_word (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) (space : PhysicalSpace) :
    Fluid.coordinateLineDerivative (field seed lag order) 0 (canonicalCauchySlicePoint time space) =
      velocityWord seed lag (order + 1) (time, space) := by
  rw [Fluid.coordinateLineDerivative_time_eq_deriv]
  simp only [field_slice]
  exact (velocityWord_hasDerivAt seed lag positive order time space).deriv

theorem coordinate_equation (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (space : PhysicalSpace) :
    Fluid.coordinateLineDerivative (field seed lag 0) 0 (canonicalCauchySlicePoint time space) =
      momentumField seed lag (time, space) := by
  rw [coordinate_word, momentumField_eq seed lag positive time valid space]
  exact positive

theorem physical_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (a b : ℝ) (a_valid : -1 < a) (b_valid : -1 < b) (space : PhysicalSpace) :
    NativeWindowSpacetimeVelocity.jointField seed lag (b, space) -
      NativeWindowSpacetimeVelocity.jointField seed lag (a, space) =
        ∫ time in a..b, momentumField seed lag (time, space) := by
  have continuousRate : Continuous (fun time => velocityWord seed lag 1 (time, space)) :=
    (velocityWord_smooth seed lag positive 1).continuous.comp (continuous_id.prodMk continuous_const)
  calc
    _ = ∫ time in a..b, velocityWord seed lag 1 (time, space) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun time _ => velocityWord_hasDerivAt seed lag positive 0 time space)
        (continuousRate.intervalIntegrable a b)).symm
    _ = _ := intervalIntegral.integral_congr (fun time inside =>
      (momentumField_eq seed lag positive time (lt_of_lt_of_le (lt_min a_valid b_valid) inside.1) space).symm)

theorem spatial_curl (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) (space : PhysicalSpace) :
    Fluid.lineCurl (field seed lag order) (canonicalCauchySlicePoint time space) =
      vorticityWord seed lag positive order (time, space) := by
  have same : NativeLineSpatialOperators.slice (field seed lag order) time =
      fun space => velocityWord seed lag order (time, space) := funext (field_slice seed lag order time)
  have smooth : ContDiff ℝ ∞ (NativeLineSpatialOperators.slice (field seed lag order) time) := by
    rw [same]
    exact (velocityWord_smooth seed lag positive order).comp (contDiff_const.prodMk contDiff_id)
  rw [NativeLineSpatialOperators.lineCurl_slice _ _ smooth, same, vorticityWord_curl]
  rfl

theorem vorticity_row_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (time : ℝ) (wave : IntegerWavevector) :
    HasDerivAt (fun sample => vorticityJet seed lag positive order sample wave)
      (vorticityJet seed lag positive (order + 1) time wave) time := by
  let read := ((fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ).comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp wholeVelocityCLM)
  exact read.hasFDerivAt.comp_hasDerivAt time (NativeWindowHeatEvolution.velocityJet_hasDerivAt seed lag order time)

theorem vorticity_momentum (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (time : ℝ) (valid : -1 < time) (wave : IntegerWavevector) :
    vorticityJet seed lag positive 1 time wave = fourierCurlCoefficient wave
      (NativeCompleteAction.momentum nu (NativeWindowHeatEvolution.source seed lag time) wave) := by
  rw [vorticity_row, momentum_row seed lag time valid]

theorem native_channels (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (modes : Finset IntegerWavevector) (time : ℝ) (valid : -1 < time) (wave : IntegerWavevector) :
    NativeCompleteEvolution.nativeRow nu modes (NativeWindowHeatEvolution.source seed lag time) wave =
      if wave ∈ modes then vorticityJet seed lag positive 1 time wave else 0 := by
  rw [NativeCompleteEvolution.nativeRow_is_complete_action, NativeCompleteAction.filteredAction,
    vorticity_momentum seed lag positive time valid]

theorem complete_native_rate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (modes : Finset IntegerWavevector) (time : ℝ) (valid : -1 < time) (wave : IntegerWavevector) :
    HasDerivAt (fun sample => if wave ∈ modes then vorticityJet seed lag positive 0 sample wave else 0)
      (NativeCompleteEvolution.nativeRHS nu modes (NativeWindowHeatEvolution.source seed lag time) wave) time := by
  rw [NativeCompleteEvolution.nativeRHS_apply, native_channels seed lag positive modes time valid]
  split_ifs
  · exact vorticity_row_hasDerivAt seed lag positive 0 time wave
  · exact hasDerivAt_const time 0

theorem physical_next (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) (space : PhysicalSpace) :
    (NativeWindowSpacetimeVelocity.jointField seed lag (response.2.clockAdvance + time, space),
      momentumField seed lag (response.2.clockAdvance + time, space),
      NativeCompleteCorrectionRead.residual (NativeWindowHeatEvolution.source seed lag (response.2.clockAdvance + time))) =
    (NativeWindowSpacetimeVelocity.jointField response.1 lag (time, space), momentumField response.1 lag (time, space),
      NativeCompleteCorrectionRead.residual (NativeWindowHeatEvolution.source response.1 lag time)) := by
  simp only [NativeWindowSpacetimeVelocity.jointField_source, momentumField]
  rw [NativeWindowHeatEvolution.source_next seed lag response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeViewPhysicalEquation
