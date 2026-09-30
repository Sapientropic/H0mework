import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Metric

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
local instance physicalMeasureRead : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbabilityRead : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativePhysicalPairing (includeCLM)
open NativeWindowFiniteGramFourier (fourierRead)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_fiber_read (M : ℕ) (v : physicalSpace (modes M))
    (k : IntegerWavevector) (i j : Coordinate) :
    NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceRecovery.fiber
      (includeCLM (modes M) (modes_closed M) v) (includeCLM (modes M) (modes_closed M) v)) k i j=
      -fourierRead k (evaluate (modes M) (modes M) i v*evaluate (modes M) (modes M) j v) := by
  change NativeCompleteStressCarrier.read (NativeCompleteStressBilinear.mixedCLM
    (NativeEndpointVelocityCarrier.wholeVelocity
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize v.1))
    (NativeEndpointVelocityCarrier.wholeVelocity
      (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize v.1))) k i j=_
  rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize v.1
    (NativeFiniteActionResolvent.physical_supported v 0 (modes_zero M)),
    NativeCompleteStressBilinear.mixedCLM_apply,NativeCompleteStressBilinear.mixed_read,
    NativeWindowHistoryCreationGeometry.product_fourier (modes M) (modes_closed M),NativeHigherTimeJets.mixedFlux]
  rw [tsum_eq_sum (s := modes M) (fun q outside => by
    simp only [NativeFiniteActionResolvent.physical_supported v q outside,Pi.zero_apply,zero_mul])]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases inside : k-q∈modes M
  · rw [if_pos inside,mul_comm]
  · simp only [if_neg inside,NativeFiniteActionResolvent.physical_supported v (k-q) inside,Pi.zero_apply,mul_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem residual_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed time M)=ᵐ[averageMeasure]
      fun lag => includeCLM (modes M) (modes_closed M) (centered seed M time (time-lag)) := by
  let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
  let m:=NativeWindowHistoryMeanProjection.mean h
  have included : m=includeCLM (modes M) (modes_closed M) (NativeWindowHistoryMeanAction.meanValue seed M time) := by
    rw [← NativeWindowHistoryCreationHalf.mean_restrict]
    exact (NativeWindowHistoryMeanPhysicalJet.include_mean seed M time).symm
  filter_upwards [Lp.coeFn_sub h (NativeWindowHistoryMeanProjection.embed m),
    NativeWindowHistoryOseen.history_original seed M time,NativeWindowTraceWholeHistory.constant_ae m]
    with lag subtract original meanRead
  change (h-NativeWindowHistoryMeanProjection.embed m) lag=_
  rw [subtract,Pi.sub_apply]
  change h lag-NativeWindowHistoryMeanProjection.embed m lag=_
  rw [show h lag=includeCLM (modes M) (modes_closed M) (NativeWindowTraceAdjoint.value seed M (time-lag)) from original,
    show NativeWindowHistoryMeanProjection.embed m lag=m from meanRead,included,← map_sub]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem covariance_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : IntegerWavevector) (i j : Coordinate) :
    fourierRead k (NativeWindowHistoryCreationCovariance.covariance seed M time i j)=
      -NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceDynamics.value seed M time) k i j := by
  let q:=NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed time M)
  have regular : Integrable (fun lag => NativeWindowHistoryCovarianceRecovery.fiber (q lag) (q lag)) averageMeasure :=
    (NativeWindowHistoryCovarianceRecovery.fiber.memLp_of_bilin 1 (Lp.memLp q) (Lp.memLp q)).integrable le_rfl
  have read:= (NativeCompleteStressCarrier.readCLM k i j).integral_comp_comm regular
  rw [← NativeWindowHistoryCovarianceRecovery.stress_integral q] at read
  simp only [NativeCompleteStressCarrier.readCLM_apply] at read
  change (∫lag,NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceRecovery.fiber (q lag) (q lag)) k i j ∂averageMeasure)=
    NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceDynamics.value seed M time) k i j at read
  rw [← read,← integral_neg,NativeWindowHistoryCreationCovariance.covariance,
    ← (fourierRead k).integral_comp_comm (NativeWindowHistoryCreationCovariance.covariance_integrable seed M time i j)]
  apply integral_congr_ae
  filter_upwards [residual_ae seed M time] with lag actual
  change q lag=_ at actual
  rw [actual,finite_fiber_read,neg_neg]

theorem covariance_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (k : IntegerWavevector) (i j : Coordinate) :
    Tendsto (fun M => fourierRead k (NativeWindowHistoryCreationCovariance.covariance seed M time i j)) atTop
      (𝓝 (-NativeCompleteStressCarrier.read ((NativeForwardWindowSource.source seed time).snd-
        NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst) k i j)) := by
  have actual:=((NativeCompleteStressCarrier.readCLM k i j).continuous.tendsto _).comp
    (NativeWindowHistoryCovarianceDynamics.value_tendsto seed time)
  simpa only [Function.comp_def,NativeCompleteStressCarrier.readCLM_apply,← covariance_original] using actual.neg


open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeFiniteActionResolvent (physical_supported physical_transverse)
open NativeCommonAdvectorAction (curlLift)

def divergenceRead (k : IntegerWavevector) (i : Coordinate) : NativeCompleteStressCarrier.Space →L[ℝ] ℂ :=
  ∑j : Coordinate,NativePhysicalGradient.multiplier k j • NativeCompleteStressCarrier.readCLM k i j

theorem divergenceRead_apply (k : IntegerWavevector) (i : Coordinate) (s : NativeCompleteStressCarrier.Space) :
    divergenceRead k i s=nativeFluidStressDivergenceCoefficient (NativeCompleteStressCarrier.read s) k i := by
  simp only [divergenceRead,sum_apply,smul_apply,smul_eq_mul,NativeCompleteStressCarrier.readCLM_apply,
    nativeFluidStressDivergenceCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold NativePhysicalGradient.multiplier
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem finite_divergence (M : ℕ) (v : physicalSpace (modes M))
    (k : IntegerWavevector) (i : Coordinate) :
    fourierRead k (advection (modes M) (modes_zero M) (modes_closed M) v v i)=
      divergenceRead k i (NativeWindowHistoryCovarianceRecovery.fiber
        (includeCLM (modes M) (modes_closed M) v) (includeCLM (modes M) (modes_closed M) v)) := by
  have tensor : NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceRecovery.fiber
      (includeCLM (modes M) (modes_closed M) v) (includeCLM (modes M) (modes_closed M) v))=
      NativeHigherTimeJets.mixedFlux v.1 v.1 := by
    change NativeCompleteStressCarrier.read (NativeCompleteStressBilinear.mixedCLM
      (NativeEndpointVelocityCarrier.wholeVelocity
        (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize v.1))
      (NativeEndpointVelocityCarrier.wholeVelocity
        (ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize v.1)))=_
    rw [NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize v.1 (physical_supported v 0 (modes_zero M)),
      NativeCompleteStressBilinear.mixedCLM_apply,NativeCompleteStressBilinear.mixed_read]
  have trans : ∀k,complexWavevector k ⬝ᵥ v.1 k=0 := by
    intro k
    by_cases inside : k∈modes M
    · exact physical_transverse v k inside
    · rw [physical_supported v k inside,dotProduct_zero]
  rw [divergenceRead_apply,tensor,NativeConvectionFlux.mixed_divergence v.1 v.1 trans,
    NativeWindowHistoryCreationGeometry.advection_fourier,
    NativeConvectionFlux.finite_convection (modes M) (curlLift (modes M) v.1) v.1
      (fun k outside => by simp [curlLift,finiteComplexVorticityState_apply,outside]) (physical_supported v),
    NativeWholeH1Cancellation.curlLift_velocity (modes M) (modes_zero M) v]

set_option backward.isDefEq.respectTransparency false in
theorem momentum_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (k : IntegerWavevector) (i : Coordinate) :
    fourierRead k (momentum seed M time i)=nativeFluidStressDivergenceCoefficient
      (NativeCompleteStressCarrier.read (NativeWindowHistoryCovarianceDynamics.value seed M time)) k i := by
  let q:=NativeWindowHistoryMeanProjection.residual (NativeWindowTraceWholeHistory.finiteHistory seed time M)
  have regular : Integrable (fun lag => NativeWindowHistoryCovarianceRecovery.fiber (q lag) (q lag)) averageMeasure :=
    (NativeWindowHistoryCovarianceRecovery.fiber.memLp_of_bilin 1 (Lp.memLp q) (Lp.memLp q)).integrable le_rfl
  have read:=(divergenceRead k i).integral_comp_comm regular
  rw [← NativeWindowHistoryCovarianceRecovery.stress_integral q] at read
  change (∫lag,divergenceRead k i (NativeWindowHistoryCovarianceRecovery.fiber (q lag) (q lag)) ∂averageMeasure)=
    divergenceRead k i (NativeWindowHistoryCovarianceDynamics.value seed M time) at read
  rw [← divergenceRead_apply,← read,momentum,← (fourierRead k).integral_comp_comm (momentum_integrable seed M time i)]
  apply integral_congr_ae
  filter_upwards [residual_ae seed M time] with lag actual
  change q lag=_ at actual
  rw [actual,finite_divergence]

theorem momentum_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (k : IntegerWavevector) (i : Coordinate) :
    Tendsto (fun M => fourierRead k (momentum seed M time i)) atTop
      (𝓝 (nativeFluidStressDivergenceCoefficient (NativeCompleteStressCarrier.read
        ((NativeForwardWindowSource.source seed time).snd-
          NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst)) k i)) := by
  have actual:=((divergenceRead k i).continuous.tendsto _).comp
    (NativeWindowHistoryCovarianceDynamics.value_tendsto seed time)
  simpa only [Function.comp_def,divergenceRead_apply,← momentum_original] using actual

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceMetric
