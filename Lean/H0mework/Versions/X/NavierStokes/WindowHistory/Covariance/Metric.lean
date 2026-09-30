import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeakPairing
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.TemporalControl
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatialTransport
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Half
import H0mework.Versions.X.NavierStokes.WindowHistory.CovarianceDynamics
import H0mework.Versions.X.NavierStokes.WindowSchurMean.PhysicalJet
import H0mework.Versions.X.NavierStokes.StressWholeH1.Cancellation

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceMetric
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier
open NativeFiniteActionResolvent (physicalSpace)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryCreationGeometry (square gradientSquare advection)
open NativeWindowHistoryCreationCovariance (centered trace)
open NativeWindowStressOseenTest (evaluate)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

private theorem real_point_young (u v : Coordinate → ℝ) (d : Coordinate → Coordinate → ℝ) :
    2*(-∑ i : Coordinate,∑ j : Coordinate,u j*v i*d j i) ≤
      (∑ j : Coordinate,(u j)^2)*(∑ i : Coordinate,(v i)^2)+∑ j : Coordinate,∑ i : Coordinate,(d j i)^2 := by
  have paid:=Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun i _ =>
      show -2*(u j*v i*d j i) ≤ (u j)^2*(v i)^2+(d j i)^2 by
        nlinarith only [sq_nonneg (u j*v i+d j i)]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul] at paid
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)] at paid
  nlinarith only [paid]

private theorem advection_continuous (M : ℕ) (i : Coordinate) :
    Continuous (fun v : physicalSpace (modes M) => advection (modes M) (modes_zero M) (modes_closed M) v v i) := by
  unfold advection
  apply Continuous.neg
  apply continuous_finsetSum
  intro j _
  exact ((LinearMap.toContinuousLinearMap (evaluate (modes M) (modes M) j)).continuous).mul
    ((LinearMap.toContinuousLinearMap (evaluate (modes M) (modes M) i)).continuous.comp
      (NativeWindowHistorySpatialTransport.finite M j).continuous)

private theorem gradient_continuous (M : ℕ) :
    Continuous (gradientSquare (modes M) (modes_zero M) (modes_closed M)) := by
  unfold gradientSquare
  apply continuous_finsetSum
  intro j _
  exact (NativeWindowHistoryCreationCovariance.square_continuous (modes M)).comp
    (NativeWindowHistorySpatialTransport.finite M j).continuous

def momentum (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (i : Coordinate) : C(Torus,ℝ) :=
  ∫lag,advection (modes M) (modes_zero M) (modes_closed M)
    (centered seed M time (time-lag)) (centered seed M time (time-lag)) i ∂averageMeasure

def fisher (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : C(Torus,ℝ) :=
  ∫lag,gradientSquare (modes M) (modes_zero M) (modes_closed M)
    (centered seed M time (time-lag)) ∂averageMeasure

theorem momentum_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (i : Coordinate) :
    Integrable (fun lag => advection (modes M) (modes_zero M) (modes_closed M)
      (centered seed M time (time-lag)) (centered seed M time (time-lag)) i) averageMeasure :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time _ ((advection_continuous M i).comp
    (NativeWindowHistoryCreationCovariance.centered_continuous seed M time)) 1).integrable le_rfl

private theorem fisher_integrable (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Integrable (fun lag => gradientSquare (modes M) (modes_zero M) (modes_closed M)
      (centered seed M time (time-lag))) averageMeasure :=
  (NativeWindowTraceTerminalGraph.continuous_memLp time _ ((gradient_continuous M).comp
    (NativeWindowHistoryCreationCovariance.centered_continuous seed M time)) 1).integrable le_rfl

private theorem trace_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    trace seed M time x=∫lag,square (modes M) (centered seed M time (time-lag)) x ∂averageMeasure :=
  ((ContinuousMap.evalCLM ℝ x).integral_comp_comm
    (NativeWindowHistoryCreationCovariance.trace_integrable seed M time)).symm

private theorem momentum_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (i : Coordinate) (x : Torus) :
    momentum seed M time i x=∫lag,advection (modes M) (modes_zero M) (modes_closed M)
      (centered seed M time (time-lag)) (centered seed M time (time-lag)) i x ∂averageMeasure :=
  ((ContinuousMap.evalCLM ℝ x).integral_comp_comm (momentum_integrable seed M time i)).symm

private theorem fisher_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    fisher seed M time x=∫lag,gradientSquare (modes M) (modes_zero M) (modes_closed M)
      (centered seed M time (time-lag)) x ∂averageMeasure :=
  ((ContinuousMap.evalCLM ℝ x).integral_comp_comm (fisher_integrable seed M time)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem advection_point_young (M : ℕ) (u : physicalSpace (modes M))
    (x : Torus) (v : Coordinate → ℝ) :
    2*(∑i : Coordinate,v i*advection (modes M) (modes_zero M) (modes_closed M) u u i x) ≤
      square (modes M) u x*(∑i : Coordinate,(v i)^2)+
        gradientSquare (modes M) (modes_zero M) (modes_closed M) u x := by
  have paid:=real_point_young (fun j => evaluate (modes M) (modes M) j u x) v
    (fun j i => evaluate (modes M) (modes M) i
      (NativeWindowAugmentedGradient.derivative (modes M) (modes_zero M) (modes_closed M) j u) x)
  have expression : (∑i : Coordinate,v i*advection (modes M) (modes_zero M) (modes_closed M) u u i x)=
      -(∑i : Coordinate,∑j : Coordinate,evaluate (modes M) (modes M) j u x*v i*
        evaluate (modes M) (modes M) i
          (NativeWindowAugmentedGradient.derivative (modes M) (modes_zero M) (modes_closed M) j u) x) := by
    simp only [advection,ContinuousMap.neg_apply,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
      mul_neg,Finset.sum_neg_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [expression]
  convert paid using 1
  simp only [square,gradientSquare,ContinuousMap.sum_apply,ContinuousMap.mul_apply,pow_two]

set_option backward.isDefEq.respectTransparency false in
theorem momentum_test (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (x : Torus) (v : Coordinate → ℝ) :
    2*(∑i : Coordinate,v i*momentum seed M time i x) ≤
      trace seed M time x*(∑i : Coordinate,(v i)^2)+fisher seed M time x := by
  have pi (i : Coordinate) := (ContinuousMap.evalCLM ℝ x).integrable_comp (momentum_integrable seed M time i)
  have si := (ContinuousMap.evalCLM ℝ x).integrable_comp
    (NativeWindowHistoryCreationCovariance.trace_integrable seed M time)
  have gi := (ContinuousMap.evalCLM ℝ x).integrable_comp (fisher_integrable seed M time)
  simp only [ContinuousMap.evalCLM_apply] at pi si gi
  simp_rw [momentum_point,← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun i _ => (pi i).const_mul (v i))]
  simp_rw [← integral_const_mul]
  rw [trace_point,fisher_point,← integral_mul_const,← integral_add (si.mul_const _) gi]
  apply integral_mono ((integrable_finsetSum Finset.univ (fun i _ => (pi i).const_mul (v i))).const_mul 2)
    ((si.mul_const _).add gi)
  intro lag
  exact advection_point_young M (centered seed M time (time-lag)) x v


theorem fisher_nonnegative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    0 ≤ fisher seed M time x := by
  rw [fisher_point]
  apply integral_nonneg
  intro lag
  simp only [gradientSquare,square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

private theorem metric_from_test (m : Coordinate → ℝ) (r g : ℝ) (r0 : 0 ≤ r)
    (test : ∀v : Coordinate → ℝ,2*(∑i,v i*m i) ≤ r*(∑i,(v i)^2)+g) :
    (∑i,(m i)^2)/(1+r) ≤ g := by
  let v:=fun i => m i/(1+r)
  have paid:=test v
  have d0 : 0 < 1+r := by linarith
  have first : (∑i,v i*m i)=(∑i,(m i)^2)/(1+r) := by
    simp only [v,div_mul_eq_mul_div,← pow_two,← Finset.sum_div]
  have second : (∑i,(v i)^2)=(∑i,(m i)^2)/(1+r)^2 := by
    simp only [v,div_pow,← Finset.sum_div]
  rw [first,second] at paid
  have positive : 0 ≤ (∑i,(m i)^2) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have reduced : r*((∑i,(m i)^2)/(1+r)^2) ≤ (∑i,(m i)^2)/(1+r) := by
    apply (le_div_iff₀ d0).mpr
    have cancel : (r*((∑i,(m i)^2)/(1+r)^2))*(1+r)=r*((∑i,(m i)^2)/(1+r)) := by field_simp
    rw [cancel]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ d0).mpr
    nlinarith only [positive]
  linarith only [paid,reduced]

theorem source_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (x : Torus) :
    (∑i : Coordinate,(momentum seed M time i x)^2)/(1+trace seed M time x) ≤ fisher seed M time x :=
  metric_from_test _ _ _ (NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time x)
    (momentum_test seed M time x)

private def spatialIntegral : C(Torus,ℝ) →L[ℝ] ℝ :=
  (L1.integralCLM' ℝ).comp (ContinuousMap.toLp 1 volume ℝ)

private theorem spatialIntegral_apply (f : C(Torus,ℝ)) : spatialIntegral f=∫x : Torus,f x := by
  rw [spatialIntegral,ContinuousLinearMap.comp_apply,← L1.integral_eq',L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (volume : Measure Torus) f] with x same
  exact same


set_option backward.isDefEq.respectTransparency false in
theorem fisher_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (∫x : Torus,fisher seed M time x)=NativeWindowTraceWholeHistory.gradient M
      (NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed time M)) := by
  rw [← spatialIntegral_apply,fisher,← spatialIntegral.integral_comp_comm (fisher_integrable seed M time)]
  simp_rw [spatialIntegral_apply,NativeWindowHistorySchurWeakPairing.gradient_integral]
  unfold NativeWindowTraceWholeHistory.gradient
  apply integral_congr_ae
  filter_upwards [NativeWindowHistoryCreationHalf.sample_centered seed M time] with lag actual
  change NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed time M) lag)=
      centered seed M time (time-lag) at actual
  exact (congrArg (fun v : physicalSpace (modes M) => NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1) actual).symm

theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    (∫x : Torus,(∑i : Coordinate,(momentum seed M time i x)^2)/(1+trace seed M time x)) ≤
      NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon := by
  have continuous : Continuous (fun x : Torus =>
      (∑i : Coordinate,(momentum seed M time i x)^2)/(1+trace seed M time x)) :=
    (continuous_finsetSum _ (fun i _ => (momentum seed M time i).continuous.pow 2)).div
      (continuous_const.add (trace seed M time).continuous)
      (fun x => ne_of_gt (by linarith [NativeWindowHistoryCreationCovariance.trace_nonnegative seed M time x]))
  have paid : (∫x : Torus,(∑i : Coordinate,(momentum seed M time i x)^2)/(1+trace seed M time x)) ≤
      ∫x : Torus,fisher seed M time x := integral_mono (continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((fisher seed M time).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (source_point seed M time)
  rw [fisher_original] at paid
  exact paid.trans ((NativeWindowHistoryMeanGradient.gradient_residual_le seed M _).trans
    (NativeWindowHistorySchurTemporalControl.source_gradient seed horizon M time inside))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceMetric
