import H0mework.NavierStokes.WindowHistoryCreation.Source
import H0mework.NavierStokes.WindowSchurMean.Blocks

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAnnihilationRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativePhysicalFourier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action)
open NativeWindowHistoryMeanProjection (mean embed residual)
open NativeWindowHistoryMeanAction (meanOperator frozen)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWindowHistoryCreationGeometry (advection transport gradientSquare)
open NativeWindowHistoryCreationCovariance (centered)
open NativeWindowFiniteGramFourier (fourierRead)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowStressHeatSource (physical)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def difference (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  action seed M time-(meanOperator seed M time).compLpL 2 averageMeasure

theorem annihilation_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    annihilation seed M time r=mean (difference seed M time r) := by
  change mean (action seed M time (r-embed (mean r)))=
    mean (action seed M time r-(meanOperator seed M time).compLpL 2 averageMeasure r)
  have first:action seed M time (r-embed (mean r))=action seed M time r-action seed M time (embed (mean r)) :=
    (action seed M time).map_sub r (embed (mean r))
  have before:=mean.map_sub (action seed M time r) (action seed M time (embed (mean r)))
  have after:=mean.map_sub (action seed M time r) ((meanOperator seed M time).compLpL 2 averageMeasure r)
  have center:mean (action seed M time (embed (mean r)))=mean ((meanOperator seed M time).compLpL 2 averageMeasure r) :=
    (NativeWindowHistoryMeanAction.mean_action seed M time (mean r)).trans
      (NativeWindowHistoryMeanProjection.mean_comp (meanOperator seed M time) r).symm
  exact ((congrArg mean first).trans before).trans
    ((congrArg (fun v : wholePhysical => mean (action seed M time r)-v) center).trans after.symm)

def input (M : ℕ) (r : H) (lag : ℝ) : physicalSpace (modes M) := restrictCLM (modes M) (modes_zero M) (modes_closed M) (r lag)

theorem input_memLp (M : ℕ) (r : H) : MemLp (input M r) 2 averageMeasure :=
  (Lp.memLp r).continuousLinearMap_comp (restrictCLM (modes M) (modes_zero M) (modes_closed M))

theorem difference_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    difference seed M time r=ᵐ[averageMeasure] fun lag => includeCLM (modes M) (modes_closed M)
      (transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M time (time-lag)) (input M r lag)) := by
  filter_upwards [Lp.coeFn_sub (action seed M time r) ((meanOperator seed M time).compLpL 2 averageMeasure r),
    NativeWindowHistoryOseen.action_ae seed M time r,(meanOperator seed M time).coeFn_compLpL r] with lag subtract actual averaged
  change (action seed M time r-(meanOperator seed M time).compLpL 2 averageMeasure r) lag=_
  rw [subtract,Pi.sub_apply,actual,averaged]
  simp only [NativeWindowHistoryOseen.forwardFiber,← NativeWindowHistoryMeanAction.frozen_source,meanOperator,
    NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply]
  rw [← map_sub]
  change includeCLM (modes M) (modes_closed M) ((frozen nu M _-frozen nu M _) (input M r lag))=_
  rw [NativeWindowHistoryCreationSource.frozen_transport]
  rfl

def output (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (annihilation seed M time r)

theorem transport_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    MemLp (fun lag => transport (modes M) (modes_zero M) (modes_closed M) nu
      (centered seed M time (time-lag)) (input M r lag)) 2 averageMeasure := by
  have paid:=(Lp.memLp (difference seed M time r)).continuousLinearMap_comp
    (restrictCLM (modes M) (modes_zero M) (modes_closed M))
  apply paid.ae_eq
  filter_upwards [difference_original seed M time r] with lag original
  rw [original,restrict_include]

theorem output_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    output seed M time r=∫lag,transport (modes M) (modes_zero M) (modes_closed M) nu
      (centered seed M time (time-lag)) (input M r lag) ∂averageMeasure := by
  rw [output,annihilation_mean,NativeWindowHistoryMeanProjection.mean_original,
    ← (restrictCLM (modes M) (modes_zero M) (modes_closed M)).integral_comp_comm ((Lp.memLp (difference seed M time r)).integrable (by norm_num))]
  apply integral_congr_ae
  filter_upwards [difference_original seed M time r] with lag original
  rw [original,restrict_include]

theorem output_include (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    includeCLM (modes M) (modes_closed M) (output seed M time r)=annihilation seed M time r := by
  rw [output_integral,← (includeCLM (modes M) (modes_closed M)).integral_comp_comm
    ((transport_memLp seed M time r).integrable (by norm_num)),annihilation_mean,NativeWindowHistoryMeanProjection.mean_original]
  exact integral_congr_ae (difference_original seed M time r).symm

def read (M : ℕ) (i : Coordinate) : physicalSpace (modes M) →L[ℝ] C(Torus,ℝ) :=
  LinearMap.toContinuousLinearMap (evaluate (modes M) (modes M) i)

def gradientRead (M : ℕ) (j i : Coordinate) : physicalSpace (modes M) →L[ℝ] C(Torus,ℝ) :=
  (read M i).comp (LinearMap.toContinuousLinearMap (NativeWindowStageNineWords.spatialGenerator (modes M) (modes_zero M) (modes_closed M) j))

def advectionMap (M : ℕ) (i : Coordinate) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) →L[ℝ] C(Torus,ℝ) :=
  -∑ j : Coordinate,(ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp (read M j) (gradientRead M j i)

theorem advectionMap_original (M : ℕ) (i : Coordinate) (u v : physicalSpace (modes M)) :
    advectionMap M i u v=advection (modes M) (modes_zero M) (modes_closed M) u v i := by
  simp only [advectionMap,neg_apply,sum_apply,ContinuousLinearMap.bilinearComp_apply,
    advection,read,gradientRead,ContinuousLinearMap.comp_apply]
  rfl

theorem advection_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) (i : Coordinate) :
    Integrable (fun lag => advection (modes M) (modes_zero M) (modes_closed M)
      (centered seed M time (time-lag)) (input M r lag) i) averageMeasure := by
  have center:=NativeWindowTraceTerminalGraph.continuous_memLp time (centered seed M time)
    (NativeWindowHistoryCreationCovariance.centered_continuous seed M time) 2
  have paid:=(ContinuousLinearMap.memLp_of_bilin 1 (advectionMap M i) center (input_memLp M r)).integrable le_rfl
  simpa only [advectionMap_original] using paid

def current (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) (i : Coordinate) : C(Torus,ℝ) :=
  ∫lag,advection (modes M) (modes_zero M) (modes_closed M) (centered seed M time (time-lag)) (input M r lag) i ∂averageMeasure

theorem current_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) (i : Coordinate) (point : Torus) :
    current seed M time r i point=∫lag,
      advection (modes M) (modes_zero M) (modes_closed M) (centered seed M time (time-lag)) (input M r lag) i point ∂averageMeasure := by
  change (ContinuousMap.evalCLM ℝ point) (∫lag,advection (modes M) (modes_zero M) (modes_closed M)
    (centered seed M time (time-lag)) (input M r lag) i ∂averageMeasure)=_
  exact ((ContinuousMap.evalCLM ℝ point).integral_comp_comm (advection_integrable seed M time r i)).symm

theorem output_row (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) (k : IntegerWavevector) :
    (output seed M time r).1 k=if k∈modes M then transverseProjection k (fun i => fourierRead k (current seed M time r i)) else 0 := by
  let V:=fun lag => transport (modes M) (modes_zero M) (modes_closed M) nu (centered seed M time (time-lag)) (input M r lag)
  let Z:=fun lag i => fourierRead k (advection (modes M) (modes_zero M) (modes_closed M)
    (centered seed M time (time-lag)) (input M r lag) i)
  have vectorPaid:Integrable Z averageMeasure := integrable_pi_iff.mpr fun i =>
    (fourierRead k).integrable_comp (advection_integrable seed M time r i)
  have row:(output seed M time r).1 k=∫lag,(V lag).1 k ∂averageMeasure := by
    have paid:=((NativeCommonAdvectorAction.evaluation k).comp (physicalSpace (modes M)).subtypeL).integral_comp_comm
      ((transport_memLp seed M time r).integrable (by norm_num))
    rw [← output_integral] at paid
    exact paid.symm
  rw [row]
  simp only [V,NativeWindowHistoryCreationGeometry.transport_row]
  by_cases inside : k∈modes M
  · simp only [if_pos inside]
    change (∫lag,(transverseProjectionCLM k) (Z lag) ∂averageMeasure)=_
    rw [(transverseProjectionCLM k).integral_comp_comm vectorPaid]
    change transverseProjection k (∫lag,Z lag ∂averageMeasure)=transverseProjection k _
    apply congrArg (transverseProjection k)
    funext i
    have applied:=(ContinuousLinearMap.proj (R := ℝ) (i := i)).integral_comp_comm vectorPaid
    change (∫lag,Z lag i ∂averageMeasure)=(∫lag,Z lag ∂averageMeasure) i at applied
    rw [← applied]
    exact (fourierRead k).integral_comp_comm (advection_integrable seed M time r i)
  · simp only [if_neg inside,integral_zero]

theorem pressure_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (r : H) :
    ‖annihilation seed M time r‖^2≤∑ i : Coordinate,‖physical (current seed M time r i)‖^2 := by
  rw [← output_include seed M time r,include_norm (modes M) (modes_zero M) (modes_closed M),← real_inner_self_eq_norm_sq]
  change pairing (modes M) (output seed M time r) (output seed M time r)≤_
  rw [pairing_eq]
  simp only [complexCoordinateRealInner_self,output_row]
  calc
    _≤∑ k∈modes M,complexCoordinateVectorNormSq (fun i => fourierRead k (current seed M time r i)) := by
      apply Finset.sum_le_sum
      intro k inside
      rw [if_pos inside]
      exact transverseProjection_amplitudeSq_le k (fun h => modes_zero M (h ▸ inside)) _
    _=∑ i : Coordinate,∑ k∈modes M,‖fourierRead k (current seed M time r i)‖^2 := by
      simp only [complexCoordinateVectorNormSq,Complex.normSq_eq_norm_sq]
      rw [Finset.sum_comm]
    _≤_ := Finset.sum_le_sum fun i _ => NativeWindowHistoryCreationGeometry.fourier_square _ (modes M)

def gradientBilinear (M : ℕ) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) →L[ℝ] C(Torus,ℝ) :=
  ∑ j : Coordinate,∑ i : Coordinate,(ContinuousLinearMap.mul ℝ C(Torus,ℝ)).bilinearComp (gradientRead M j i) (gradientRead M j i)

theorem gradientBilinear_original (M : ℕ) (v : physicalSpace (modes M)) :
    gradientBilinear M v v=gradientSquare (modes M) (modes_zero M) (modes_closed M) v := by
  simp only [gradientBilinear,sum_apply,ContinuousLinearMap.bilinearComp_apply,gradientRead,read,
    ContinuousLinearMap.comp_apply,gradientSquare,NativeWindowHistoryCreationGeometry.square]
  rfl

theorem gradient_integrable (M : ℕ) (r : H) :
    Integrable (fun lag => gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag)) averageMeasure := by
  simpa only [gradientBilinear_original] using
    (ContinuousLinearMap.memLp_of_bilin 1 (gradientBilinear M) (input_memLp M r) (input_memLp M r)).integrable le_rfl

def averageGradient (M : ℕ) (r : H) : C(Torus,ℝ) :=
  ∫lag,gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag) ∂averageMeasure

theorem averageGradient_point (M : ℕ) (r : H) (point : Torus) : averageGradient M r point=∫lag,
    gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag) point ∂averageMeasure := by
  change (ContinuousMap.evalCLM ℝ point) (∫lag,gradientSquare (modes M) (modes_zero M) (modes_closed M) (input M r lag) ∂averageMeasure)=_
  exact ((ContinuousMap.evalCLM ℝ point).integral_comp_comm (gradient_integrable M r)).symm

theorem center_read_memLp (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (j : Coordinate) :
    MemLp (fun lag => read M j (centered seed M time (time-lag))) 2 averageMeasure :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time (centered seed M time)
    (NativeWindowHistoryCreationCovariance.centered_continuous seed M time) 2).continuousLinearMap_comp (read M j)

theorem gradient_read_memLp (M : ℕ) (r : H) (j i : Coordinate) :
    MemLp (fun lag => gradientRead M j i (input M r lag)) 2 averageMeasure :=
  (input_memLp M r).continuousLinearMap_comp (gradientRead M j i)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAnnihilationRows
