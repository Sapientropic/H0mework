import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Physical
import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.TimeAction
import H0mework.Versions.X.NavierStokes.PhysicalView.ConsumerNext

/-! The existing emitted carrier supplies its zero-heat physical observations.
Its clock, compiled ledger and next current remain the original runtime operations. -/

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowTailRootConsumer
open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeWindowRootControl NativeWindowSpacetimeFourier
open NativeFullOrderSynthesis NativeEndpointVelocityCarrier NativeWindowLocalFourier
noncomputable section
variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}
    {current : NativeTemporalCurrent initial} {occurrence : Occurrence initial current}

def velocity (carrier : CarrierAt initial occurrence) (point : Spacetime) : PhysicalSpace :=
  spatialField (wholeVelocity (carrier.view 0 point.1).fst) point.2

def stress (carrier : CarrierAt initial occurrence) (point : Spacetime) :
    EuclideanSpace ℝ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun entry => (∑' wave,
    NativeCompleteStressCarrier.read (carrier.view 0 point.1).snd wave entry.1 entry.2 * monomial wave point.2).re

def residual (carrier : CarrierAt initial occurrence) (point : Spacetime) :
    EuclideanSpace ℝ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun entry => (∑' wave,
    NativeCompleteCorrectionRead.residual (carrier.view 0 point.1) wave entry.1 entry.2 * monomial wave point.2).re

def support (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) : Set Spacetime :=
  (chart initial current) ⁻¹' NativeWindowTailPhysical.support initial

theorem support_open (initial : GeneratedWholeRestartCurrent nu) (current : NativeTemporalCurrent initial) :
    IsOpen (support initial current) :=
  (NativeWindowTailPhysical.support_open initial).preimage (chart_smooth initial current).continuous

theorem source_read (carrier : CarrierAt initial occurrence) (time : ℝ) :
    carrier.view 0 time = NativeForwardWindowSource.source initial (clockAt initial current + time) := by
  rw [CarrierAt.view_generated, NativeZeroHeatWindow.source_zero]

theorem velocity_generated (carrier : CarrierAt initial occurrence) :
    velocity carrier = NativeWindowSpacetimeVelocity.jointField initial 0 ∘ chart initial current := by
  funext point
  rw [velocity, CarrierAt.view_generated, Function.comp_apply, NativeWindowSpacetimeVelocity.jointField_source]
  rfl

theorem stress_generated (carrier : CarrierAt initial occurrence) :
    stress carrier = NativeWindowSpacetimeStress.jointField initial 0 ∘ chart initial current := by
  funext point
  apply PiLp.ext
  intro entry
  rw [Function.comp_apply, NativeWindowSpacetimeStress.jointField_source]
  change (∑' wave, NativeCompleteStressCarrier.read (carrier.view 0 point.1).snd wave entry.1 entry.2 * monomial wave point.2).re = _
  rw [CarrierAt.view_generated]
  rfl

theorem residual_generated (carrier : CarrierAt initial occurrence) :
    residual carrier = NativeWindowSpacetimeResidual.jointField initial 0 ∘ chart initial current := by
  funext point
  apply PiLp.ext
  intro entry
  rw [Function.comp_apply, NativeWindowSpacetimeResidual.jointField_source]
  change (∑' wave, NativeCompleteCorrectionRead.residual (carrier.view 0 point.1) wave entry.1 entry.2 * monomial wave point.2).re = _
  rw [CarrierAt.view_generated]
  rfl

theorem velocity_smooth (carrier : CarrierAt initial occurrence) :
    ContDiffOn ℝ ∞ (velocity carrier) (support initial current) := by
  rw [velocity_generated]
  exact (NativeWindowTailPhysical.velocity_smooth initial).comp
    (chart_smooth initial current).contDiffOn (fun _ inside => inside)

theorem stress_smooth (carrier : CarrierAt initial occurrence) :
    ContDiffOn ℝ ∞ (stress carrier) (support initial current) := by
  rw [stress_generated]
  exact (NativeWindowTailPhysical.stress_smooth initial).comp
    (chart_smooth initial current).contDiffOn (fun _ inside => inside)

theorem residual_smooth (carrier : CarrierAt initial occurrence) :
    ContDiffOn ℝ ∞ (residual carrier) (support initial current) := by
  rw [residual_generated]
  exact (NativeWindowTailPhysical.residual_smooth initial).comp
    (chart_smooth initial current).contDiffOn (fun _ inside => inside)

def vorticity (carrier : CarrierAt initial occurrence) (point : Spacetime) : PhysicalSpace :=
  NativeViewPhysicalCurl.jointCurlRead (fderiv ℝ (velocity carrier) point)

def rate (carrier : CarrierAt initial occurrence) (point : Spacetime) : PhysicalSpace :=
  fderiv ℝ (velocity carrier) point (1, 0)

theorem vorticity_actual (carrier : CarrierAt initial occurrence) (point : Spacetime)
    (inside : point ∈ support initial current) :
    vorticity carrier point = NativeTimeChartVorticityReadout.spatialCurl
      (fun space => velocity carrier (point.1, space)) point.2 := by
  have differentiable := ((velocity_smooth carrier point inside).contDiffAt
    ((support_open initial current).mem_nhds inside)).differentiableAt (by simp)
  have curve : HasFDerivAt (fun space : PhysicalSpace => (point.1, space))
      ((0 : PhysicalSpace →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ PhysicalSpace)) point.2 :=
    (hasFDerivAt_const point.1 point.2).prodMk (hasFDerivAt_id point.2)
  have written : fderiv ℝ (fun space => velocity carrier (point.1, space)) point.2 =
      (fderiv ℝ (velocity carrier) point).comp
        ((0 : PhysicalSpace →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ PhysicalSpace)) := by
    simpa only [Function.comp_def] using (differentiable.hasFDerivAt.comp point.2 curve).fderiv
  rw [vorticity, NativeTimeChartVorticityReadout.spatialCurl, written,
    NativeViewPhysicalCurl.jointCurlRead_apply]
  rfl

theorem physical_hasDerivAt (carrier : CarrierAt initial occurrence) (point : Spacetime)
    (inside : point ∈ support initial current) :
    HasDerivAt (fun time => velocity carrier (time, point.2)) (rate carrier point) point.1 := by
  have differentiable := ((velocity_smooth carrier point inside).contDiffAt
    ((support_open initial current).mem_nhds inside)).differentiableAt (by simp)
  exact differentiable.hasFDerivAt.comp_hasDerivAt point.1
    ((hasDerivAt_id point.1).prodMk (hasDerivAt_const point.1 point.2))

theorem rate_momentum (carrier : CarrierAt initial occurrence) (point : Spacetime)
    (inside : point ∈ support initial current) :
    rate carrier point = NativeViewPhysicalEquation.momentumField initial 0 (chart initial current point) := by
  have source := (NativeTailTimeAction.physical_hasDerivAt initial
    (clockAt initial current + point.1) inside.1 point.2).scomp point.1
      ((hasDerivAt_id point.1).const_add (clockAt initial current))
  have received : HasDerivAt (fun time => velocity carrier (time, point.2))
      (NativeViewPhysicalEquation.momentumField initial 0 (chart initial current point)) point.1 := by
    simpa only [velocity_generated, Function.comp_apply, chart, Function.comp_def, one_smul] using! source
  exact (physical_hasDerivAt carrier point inside).unique received

def outputs (carrier : CarrierAt initial occurrence) (point : Spacetime) :=
  ((velocity carrier point, stress carrier point, residual carrier point),
    vorticity carrier point, rate carrier point)

theorem outputs_smooth (carrier : CarrierAt initial occurrence) :
    ContDiffOn ℝ ∞ (outputs carrier) (support initial current) := by
  have derivative := (contDiffOn_infty_iff_fderiv_of_isOpen
    (support_open initial current)).mp (velocity_smooth carrier) |>.2
  have curlSmooth := NativeViewPhysicalCurl.jointCurlRead.contDiff.comp_contDiffOn derivative
  have timeSmooth := (ContinuousLinearMap.apply ℝ PhysicalSpace ((1, 0) : Spacetime)).contDiff.comp_contDiffOn derivative
  exact ((velocity_smooth carrier).prodMk ((stress_smooth carrier).prodMk (residual_smooth carrier))).prodMk
    (curlSmooth.prodMk timeSmooth)

theorem all_order_control (carrier : CarrierAt initial occurrence) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ support initial current) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (outputs carrier)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (outputs carrier)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp_on _ (outputs_smooth carrier) (support_open initial current) order exponent compact contained

open NativeViewRuntime NativeViewConsumerNext

def read (runtime : Runtime) (point : Spacetime) := outputs (payload runtime) point

theorem read_all_order_control (runtime : Runtime) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain)
    (contained : domain ⊆ support NativeViewRuntime.initial (visit (index runtime)).current) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (read runtime)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (read runtime)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  all_order_control (payload runtime) order exponent compact contained

theorem measured_next (runtime : Runtime) (time : ℝ) :
    (payload runtime.tick.next).view 0 time =
      (payload runtime).view 0 (advance runtime + time) := by
  erw [CarrierAt.view_generated, CarrierAt.view_generated]
  simp only [index_next, visit_current]
  change NativeWindowHeatEvolution.source initial 0 (elapsedTime initial (index runtime + 1) + time) = _
  rw [elapsedTime_succ, add_assoc]
  rfl

theorem controller_write_back (runtime : Runtime) :
    HEq (facade.readoutAt runtime PUnit.unit)
      (runtime.tick.generated.projectionOutcome ((installation NativeViewRuntime.initial).embed resolution)) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        ((nativeTemporalRoot NativeViewRuntime.initial).generatedLedgerAt (visit runtime.state).current) ∧
      runtime.tick.nextCurrent = process.stateAt (process.successor runtime.state) ∧
      (∀ time, (payload runtime.tick.next).view 0 time =
        (payload runtime).view 0 (advance runtime + time)) :=
  ⟨(activated_readout runtime).1, (activated_readout runtime).2.1,
    (activated_readout runtime).2.2, measured_next runtime⟩

end
end SaturationMonoid.NavierStokes.NativeWindowTailRootConsumer
