import H0mework.Versions.X.NavierStokes.PhysicalView.RootPreparation
import H0mework.Versions.X.NavierStokes.SourcePairing.SpacetimeEquation
import H0mework.Versions.X.NavierStokes.WindowPhysics.RootCompleteControl

set_option autoImplicit false
open scoped Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeViewObservation

open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeWindowRootControl NativeWindowSpacetimeFourier NativeFullOrderSynthesis
open NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

/-- The measuring operation consumes the source history carried by this exact occurrence. -/
def measure (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : NativeCompleteStressAction.FullSpace :=
  NativeViewPreparation.predict nu query.1 carrier.history time

theorem measure_view (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    measure carrier query time = carrier.view query.1 time := rfl

theorem measure_laboratory (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    measure carrier query time = NativeViewPreparation.laboratoryRead nu query.1
      (NativeUnifiedCompleteSource.source initial) (NativeViewPreparation.rootClock initial current time) :=
  NativeViewPreparation.view_laboratory_read carrier query.1 time

theorem velocity_measured (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    velocity carrier query point = spatialField (wholeVelocity (measure carrier query point.1).fst) point.2 := rfl

def vorticity (_carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace :=
  NativeViewPhysicalCurl.vorticityWord initial query.1 query.2 0 (chart initial current point)

def rate (_carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace :=
  NativeViewPhysicalTime.velocityWord initial query.1 1 (chart initial current point)

theorem vorticity_actual (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    vorticity carrier query point = NativeTimeChartVorticityReadout.spatialCurl
      (fun space => velocity carrier query (point.1, space)) point.2 := by
  rw [vorticity, NativeViewPhysicalCurl.vorticityWord_curl]
  simp only [velocity_generated, Function.comp_apply, chart, NativeViewPhysicalTime.velocityWord_zero]

theorem rate_actual (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ)
    (space : ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace) :
    HasDerivAt (fun sample => velocity carrier query (sample, space)) (rate carrier query (time, space)) time := by
  have original := (NativeViewPhysicalTime.velocityWord_hasDerivAt initial query.1 query.2 0
    (clockAt initial current + time) space).scomp time ((hasDerivAt_id time).const_add (clockAt initial current))
  simpa only [velocity_generated, Function.comp_apply, chart, rate, NativeViewPhysicalTime.velocityWord_zero,
    Function.comp_def, one_smul] using! original

theorem rate_momentum (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ)
    (nonnegative : 0 ≤ time) (space : ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace) :
    rate carrier query (time, space) =
      NativeViewPhysicalEquation.momentumField initial query.1 (clockAt initial current + time, space) :=
  (NativeViewPhysicalEquation.momentumField_eq initial query.1 query.2 _
    (by linarith [clockAt_nonnegative initial current]) space).symm

/-- The controlled outputs are measured velocity, complete stress, complete R, actual curl, and physical time rate. -/
def outputs (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :=
  (NativeWindowRootCompleteControl.fields carrier query point,
    (vorticity carrier query point, rate carrier query point))

theorem outputs_smooth (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    ContDiff ℝ ∞ (outputs carrier query) :=
  (NativeWindowRootCompleteControl.fields_smooth carrier query).prodMk
    (((NativeViewPhysicalCurl.vorticityWord_smooth initial query.1 query.2 0).comp (chart_smooth initial current)).prodMk
      ((NativeViewPhysicalTime.velocityWord_smooth initial query.1 query.2 1).comp (chart_smooth initial current)))

theorem outputs_all_order_Lp (carrier : CarrierAt initial occurrence) (query : HeatQuery)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (outputs carrier query)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (outputs carrier query)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (outputs_smooth carrier query) order exponent compact

end
end SaturationMonoid.NavierStokes.NativeViewObservation
