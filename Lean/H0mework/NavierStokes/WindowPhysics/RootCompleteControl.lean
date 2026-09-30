import H0mework.NavierStokes.WindowPhysics.RootControl
import H0mework.NavierStokes.WindowPhysics.SpacetimeResidual

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowRootCompleteControl

open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeWindowRootControl NativeWindowSpacetimeFourier NativeFullOrderSynthesis

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

def residual (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    EuclideanSpace ℝ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun entry => (∑' wave,
    NativeCompleteCorrectionRead.residual (carrier.view query.1 point.1) wave entry.1 entry.2 * monomial wave point.2).re

theorem residual_generated (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    residual carrier query = NativeWindowSpacetimeResidual.jointField initial query.1 ∘ chart initial current := by
  funext point
  apply PiLp.ext
  intro entry
  rw [Function.comp_apply, NativeWindowSpacetimeResidual.jointField_source]
  change (∑' wave, NativeCompleteCorrectionRead.residual (carrier.view query.1 point.1) wave entry.1 entry.2 * monomial wave point.2).re = _
  rw [CarrierAt.view_generated]
  rfl

theorem residual_smooth (carrier : CarrierAt initial occurrence) (query : HeatQuery) : ContDiff ℝ ∞ (residual carrier query) := by
  rw [residual_generated]
  exact (NativeWindowSpacetimeResidual.jointField_smooth initial query.1 query.2).comp (chart_smooth initial current)

def fields (carrier : CarrierAt initial occurrence) (query : HeatQuery) (point : Spacetime) :
    WithLp 2 (WithLp 2 (PhysicalSpace × EuclideanSpace ℝ (Coordinate × Coordinate)) ×
      EuclideanSpace ℝ (Coordinate × Coordinate)) :=
  WithLp.toLp 2 (physicalPair carrier query point, residual carrier query point)

theorem fields_smooth (carrier : CarrierAt initial occurrence) (query : HeatQuery) :
    ContDiff ℝ ∞ (fields carrier query) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ
    (WithLp 2 (PhysicalSpace × EuclideanSpace ℝ (Coordinate × Coordinate)))
    (EuclideanSpace ℝ (Coordinate × Coordinate))).symm.contDiff.comp
    ((physicalPair_smooth carrier query).prodMk (residual_smooth carrier query))

theorem authority_all_order_Lp (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) (query : HeatQuery)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (fields (authorityCarrier initial visit query) query)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (fields (authorityCarrier initial visit query) query)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (fields_smooth (authorityCarrier initial visit query) query) order exponent compact

theorem original_residual_retained (carrier : CarrierAt initial occurrence) (time : ℝ) :
    NativeCompleteCorrectionRead.residual (carrier.history time) =
      NativeCompleteCorrectionRead.residual (NativeUnifiedCompleteSource.source initial (clockAt initial current + time)) := by
  rw [carrier.history_eq]

end
end SaturationMonoid.NavierStokes.NativeWindowRootCompleteControl
