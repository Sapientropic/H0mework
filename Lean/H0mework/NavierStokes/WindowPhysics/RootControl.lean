import H0mework.NavierStokes.WindowPhysics.RootCarrier
import H0mework.NavierStokes.WindowPhysics.SpacetimeVelocity
import H0mework.NavierStokes.WindowPhysics.SpacetimeStress

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowRootControl

open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeWindowSpacetimeFourier NativeFullOrderSynthesis
open NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

def velocity (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) : PhysicalSpace :=
  spatialField (wholeVelocity (carrier.view query.1 point.1).fst) point.2

def stress (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    EuclideanSpace ℝ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun entry => (∑' wave,
    NativeCompleteStressCarrier.read (carrier.view query.1 point.1).snd wave entry.1 entry.2 * monomial wave point.2).re

def chart (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) (point : Spacetime) : Spacetime :=
  (clockAt initial current + point.1, point.2)

theorem chart_smooth (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) :
    ContDiff ℝ ∞ (chart initial current) :=
  (contDiff_const.add contDiff_fst).prodMk contDiff_snd

theorem velocity_generated (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    velocity carrier query = NativeWindowSpacetimeVelocity.jointField initial query.1 ∘ chart initial current := by
  funext point
  rw [velocity, CarrierAt.view_generated, Function.comp_apply, NativeWindowSpacetimeVelocity.jointField_source]
  rfl

theorem stress_generated (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    stress carrier query = NativeWindowSpacetimeStress.jointField initial query.1 ∘ chart initial current := by
  funext point
  apply PiLp.ext
  intro entry
  rw [Function.comp_apply, NativeWindowSpacetimeStress.jointField_source]
  change (∑' wave, NativeCompleteStressCarrier.read (carrier.view query.1 point.1).snd wave entry.1 entry.2 * monomial wave point.2).re = _
  rw [CarrierAt.view_generated]
  rfl

theorem velocity_smooth (carrier : CarrierAt initial occurrence) (query : HeatQuery) : ContDiff ℝ ∞ (velocity carrier query) := by
  rw [velocity_generated]
  exact (NativeWindowSpacetimeVelocity.jointField_smooth initial query.1 query.2).comp (chart_smooth initial current)

theorem stress_smooth (carrier : CarrierAt initial occurrence) (query : HeatQuery) : ContDiff ℝ ∞ (stress carrier query) := by
  rw [stress_generated]
  exact (NativeWindowSpacetimeStress.jointField_smooth initial query.1 query.2).comp (chart_smooth initial current)

def physicalPair (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    WithLp 2 (PhysicalSpace × EuclideanSpace ℝ (Coordinate × Coordinate)) :=
  WithLp.toLp 2 (velocity carrier query point, stress carrier query point)

theorem physicalPair_smooth (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    ContDiff ℝ ∞ (physicalPair carrier query) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ PhysicalSpace (EuclideanSpace ℝ (Coordinate × Coordinate))).symm.contDiff.comp
    ((velocity_smooth carrier query).prodMk (stress_smooth carrier query))

def authorityCarrier (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) (query : HeatQuery) :
    CarrierAt initial ((world initial).authoritativeEvolutionAt visit).toLedgerReadout.occurrence :=
  match ((world initial).authoritativeEvolutionAt visit).toLedgerReadout.projectionOutcome
      (world := world initial) ((installation initial).embed query) with
  | .inl ⟨_, payload⟩ => payload
  | .inr impossible => nomatch impossible

theorem authority_all_order_Lp (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) (query : HeatQuery)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (physicalPair (authorityCarrier initial visit query) query)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (physicalPair (authorityCarrier initial visit query) query)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (physicalPair_smooth (authorityCarrier initial visit query) query) order exponent compact

theorem authority_actual_rate (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) (query : HeatQuery)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivAt (fun sample => NativeNegativeFourMomentum.embed
      ((authorityCarrier initial visit query).view query.1 sample).fst)
      (NativeCompleteStressAction.momentumCLM nu ((authorityCarrier initial visit query).view query.1 time)) time :=
  (authorityCarrier initial visit query).physical_hasDerivAt query time
    (by linarith [clockAt_nonnegative initial visit.current])

end
end SaturationMonoid.NavierStokes.NativeWindowRootControl
