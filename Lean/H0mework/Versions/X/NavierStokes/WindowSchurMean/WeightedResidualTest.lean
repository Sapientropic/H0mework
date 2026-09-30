import H0mework.Versions.X.NavierStokes.WindowSchurMean.PhysicalResidualCost
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Complete.Variational

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanWeightedResidualTest
open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeWholeH1Mixed (modes)
open NativeWholeResolvent (wholePhysical)
open NativeEndpointVelocityCarrier (wholeVelocity)
open NativeTimeJetCarrier (projectedDivergenceCLM projectedDivergenceCLM_apply)
open NativeCompleteStressAction (euclideanCLM)
open NativeWholeH1Cancellation (row_real_inner)
open NativeCompleteCovariance (Test TestIndex action component)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def waveTest (M : ℕ) (l : wholePhysical) (i : Coordinate) : Test :=
  ∑k∈modes M,
    (Finsupp.single (k,false) ((wholeVelocity l.1 k i).re)+
      Finsupp.single (k,true) ((wholeVelocity l.1 k i).im))

theorem action_waveTest (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (l : wholePhysical) (i : Coordinate) :
    action seed time i (waveTest M l i)=
      ∑k∈modes M,
        ((wholeVelocity l.1 k i).re*
            (NativeWindowHistoryCovarianceMetric.divergenceRead k i
              (NativeCompleteCovariance.residual seed time)).re+
          (wholeVelocity l.1 k i).im*
            (NativeWindowHistoryCovarianceMetric.divergenceRead k i
              (NativeCompleteCovariance.residual seed time)).im) := by
  simp only [waveTest, map_sum, map_add]
  simp [NativeCompleteCovariance.action,NativeCompleteCovariance.component]

def stressDivergence (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (k : IntegerWavevector) : ComplexCoordinateVector :=
  fun i => NativeWindowHistoryCovarianceMetric.divergenceRead k i
    (NativeCompleteCovariance.residual seed time)

theorem stressRow_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (k : NonzeroIntegerWavevector) :
    NativeViewEnergyWork.residualRow seed 0 time k=
      euclideanCLM (transverseProjection k.1 (stressDivergence seed time k.1)) := by
  rw [NativeViewEnergyWork.residualRow,NativeZeroHeatWindow.source_zero,
    projectedDivergenceCLM_apply]
  change euclideanCLM (transverseProjection k.1
    (nativeFluidStressDivergenceCoefficient
      (NativeCompleteStressCarrier.read (NativeCompleteCovariance.residual seed time)) k.1))=_
  have div : nativeFluidStressDivergenceCoefficient
      (NativeCompleteStressCarrier.read (NativeCompleteCovariance.residual seed time)) k.1=
        stressDivergence seed time k.1 := by
    funext i
    exact (NativeWindowHistoryCovarianceMetric.divergenceRead_apply k.1 i
      (NativeCompleteCovariance.residual seed time)).symm
  rw [div]

theorem stressRow_pair (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (l : wholePhysical) (k : NonzeroIntegerWavevector) :
    inner ℝ (l.1 k) (NativeViewEnergyWork.residualRow seed 0 time k)=
      ∑i : Coordinate,
        ((l.1 k i).re*(stressDivergence seed time k.1 i).re+
          (l.1 k i).im*(stressDivergence seed time k.1 i).im) := by
  rw [stressRow_read]
  have row : l.1 k=euclideanCLM (wholeVelocity l.1 k.1) := by
    apply PiLp.ext
    intro i
    exact (NativeEndpointVelocityCarrier.wholeVelocity_nonzero l.1 k i).symm
  rw [row]
  change inner ℝ (euclideanCoordinateRow (wholeVelocity l.1 k.1))
    (euclideanCoordinateRow (transverseProjection k.1 (stressDivergence seed time k.1)))=_
  rw [row_real_inner,complexCoordinateRealInner_transverseProjection k.1 _ _ k.2
    (NativeWholeResolvent.whole_transverse l k.1)]
  rfl

private theorem sum_nonzero (M : ℕ) (f : IntegerWavevector→ℝ) :
    (∑k : (modes M).subtype (fun k => k≠0),f k.1.1)=∑k∈modes M,f k := by
  exact (Finset.sum_coe_sort ((modes M).subtype (fun k => k≠0)) (fun k => f k.1)).trans
    (Finset.sum_subtype_of_mem f (fun k member (zero : k=0) =>
      NativeWholeH1Mixed.modes_zero M (zero ▸ member)))

theorem stressWork_action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryMeanPhysicalResidualCost.stressWork seed M time=
      ∑i : Coordinate,action seed time i
        (waveTest M (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
          (NativeWindowHistoryMeanProjection.mean
            (NativeWindowTraceWholeHistory.finiteHistory seed time M))) i) := by
  let l := NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
    (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  let f := fun (k : IntegerWavevector) (i : Coordinate) =>
    (wholeVelocity l.1 k i).re*(stressDivergence seed time k i).re+
      (wholeVelocity l.1 k i).im*(stressDivergence seed time k i).im
  have original : NativeWindowHistoryMeanPhysicalResidualCost.stressWork seed M time=
      ∑k∈modes M,∑i : Coordinate,f k i := by
    unfold NativeWindowHistoryMeanPhysicalResidualCost.stressWork
    change (∑k : (modes M).subtype (fun k => k≠0),
      inner ℝ (l.1 k.1) (NativeViewEnergyWork.residualRow seed 0 time k.1))=_
    simp_rw [stressRow_pair]
    have row (k : NonzeroIntegerWavevector) (i : Coordinate) :
        l.1 k i=wholeVelocity l.1 k.1 i :=
      (NativeEndpointVelocityCarrier.wholeVelocity_nonzero l.1 k i).symm
    simp_rw [row]
    exact sum_nonzero M (fun k => ∑i : Coordinate,f k i)
  rw [original]
  simp_rw [action_waveTest]
  change (∑k∈modes M,∑i : Coordinate,f k i)=
    ∑i : Coordinate,∑k∈modes M,f k i
  exact Finset.sum_comm

def weightedTestCost (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  let l := NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
    (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  ∑i : Coordinate,‖NativeCompleteCovariance.testMap seed time (waveTest M l i)‖^2

theorem weightedTestCost_physical (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    weightedTestCost seed M time=
      ∑i : Coordinate,∫x : NativePhysicalFourier.Torus,
        NativeCompleteCovariance.density seed time x*
          (NativeCompleteCovariance.polynomial
            (waveTest M (NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
              (NativeWindowHistoryMeanProjection.mean
                (NativeWindowTraceWholeHistory.finiteHistory seed time M))) i) x)^2 := by
  unfold weightedTestCost
  simp_rw [NativeCompleteCovariance.weighted_square]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem weightedTestCost_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (nonnegative : 0≤time) :
    weightedTestCost seed M (step.2.clockAdvance+time)=
      weightedTestCost step.1 M time := by
  rw [weightedTestCost_physical,weightedTestCost_physical]
  simp only [NativeCompleteCovariance.density,
    NativeWindowHistoryCovarianceLimit.value_next seed step generated time nonnegative,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time nonnegative M]

theorem source_stress_weighted_test (seed : GeneratedWholeRestartCurrent nu)
    (horizon time : ℝ) (inside : time∈Icc 0 horizon) (M : ℕ) :
    NativeWindowHistoryMeanPhysicalResidualCost.stressWork seed M time≤
      Real.sqrt (NativeCompleteCovariance.budget seed horizon)*
        Real.sqrt (3*weightedTestCost seed M time) := by
  let l := NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
    (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))
  let q := fun i : Coordinate => ‖NativeCompleteCovariance.testMap seed time (waveTest M l i)‖
  have point (i : Coordinate) : action seed time i (waveTest M l i)≤
      Real.sqrt (NativeCompleteCovariance.budget seed horizon)*q i :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      NativeCompleteCovariance.source_test_bound seed horizon time inside i (waveTest M l i))
  have summed:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  rw [← Finset.mul_sum] at summed
  have cs : (∑i : Coordinate,q i)^2≤3*(∑i : Coordinate,(q i)^2) := by
    have bound:=Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ)
      (fun _ : Coordinate => (1:ℝ)) q
    simpa [Fin.sum_univ_three] using bound
  have sqrtBound : (∑i : Coordinate,q i)≤Real.sqrt (3*weightedTestCost seed M time) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [weightedTestCost,q,l] using cs
  have nonnegative : 0≤Real.sqrt (NativeCompleteCovariance.budget seed horizon) := Real.sqrt_nonneg _
  rw [stressWork_action]
  exact summed.trans (mul_le_mul_of_nonneg_left sqrtBound nonnegative)

theorem source_weighted_spatial_cost (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,
      (nu.coeff/4)*‖NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
        (NativeWindowHistoryMeanProjection.mean
          (NativeWindowTraceWholeHistory.finiteHistory seed t M))‖^2≤
          Real.sqrt (NativeCompleteCovariance.budget seed horizon)*
            Real.sqrt (3*weightedTestCost seed M t)+C := by
  obtain ⟨low,C,C0,paid⟩:=
    NativeWindowHistoryMeanPhysicalResidualCost.source_stress_spatial_cost seed horizon
  refine ⟨low,C,C0,fun M above t inside => ?_⟩
  exact (paid M above t inside).trans
    (add_le_add_left (source_stress_weighted_test seed horizon t inside M) C)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanWeightedResidualTest
