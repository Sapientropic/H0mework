import H0mework.Versions.X.NavierStokes.WindowSchurMean.Projection
import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowEvolution
import H0mework.NavierStokes.StressEvolutionTemporalVariation.MovingProjection

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open NativeResolventCompactness NativeWholeResolvent NativePhysicalPairing NativeEndpointVelocityCarrier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowTraceWholeHistory (H finiteHistory)
open NativeWindowHistoryMeanProjection (mean)
noncomputable section
variable {nu : Viscosity}

def read (M : ℕ) : State →L[ℝ] State :=
  (puncturedEuclideanizeCLM.restrictScalars ℝ).comp
    ((NativeCorrectionTime.projectionCLM (modes M)).comp wholeVelocityCLM)

theorem read_original (M : ℕ) (v : State) :
    read M v=wholeRestartVelocityEndpointGalerkinInitialVelocity M v := by
  apply lp.ext
  funext k
  apply PiLp.ext
  intro i
  simp only [read,ContinuousLinearMap.comp_apply,
    NativeCorrectionTime.projectionCLM_apply,wholeVelocityCLM_apply]
  change complexSharpSupportProjection (modes M) (wholeVelocity v) k.1 i=_
  rw [complexSharpSupportProjection_apply,wholeRestartVelocityEndpointGalerkinInitialVelocity_apply]
  by_cases included : k.1∈modes M
  · have covered : k.1∈ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay.wholeRestartModes M:=included
    rw [if_pos included,if_pos covered]
    exact wholeVelocity_nonzero v k i
  · have covered : k.1∉ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay.wholeRestartModes M:=included
    rw [if_neg included,if_neg covered]
    rfl

theorem read_bound (M : ℕ) (v : State) : ‖read M v‖≤‖v‖ := by
  rw [read_original]
  exact NativeGalerkinMovingProjection.projection_norm_le M v

theorem projection_read (M : ℕ) (v : wholePhysical) :
    (NativeWindowTraceWholeHistory.projection M v).1=read M v.1 := by
  simp only [read,ContinuousLinearMap.comp_apply,NativeCorrectionTime.projectionCLM_apply]
  rfl

def jet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : State :=
  read M (NativeForwardWindowEvolution.velocityJet seed order time)

theorem jet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (jet seed M order) (jet seed M (order+1) time) time :=
  (read M).hasFDerivAt.comp_hasDerivAt time (NativeForwardWindowEvolution.velocityJet_hasDerivAt seed order time)

theorem jet_bound (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    ‖jet seed M order time‖≤NativeForwardWindowJets.budget seed order :=
  (read_bound M _).trans (NativeForwardWindowEvolution.velocityJet_bound seed order time)

theorem source_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (mean (finiteHistory seed time M)).1=jet seed M 0 time := by
  have same:=NativeWindowHistoryMeanProjection.mean_comp (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowTraceWholeHistory.history seed time)
  have readback:=congrArg (fun v : wholePhysical => v.1) same
  change (mean (finiteHistory seed time M)).1=_ at readback
  rw [projection_read,NativeWindowHistoryMeanProjection.source_mean] at readback
  simpa only [jet,NativeForwardWindowEvolution.velocityJet,NativeForwardWindowJets.jet_zero] using readback

theorem source_rate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    (mean (NativeWindowHistoryOseen.rateHistory seed M time)).1=jet seed M 1 time := by
  let L : H →L[ℝ] State:=(wholePhysical.subtypeL).comp mean
  have actual:=L.hasFDerivAt.comp_hasDerivAt (E := State) (F := H) time (NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  have original : HasDerivAt (jet seed M 0)
      (mean (NativeWindowHistoryOseen.rateHistory seed M time)).1 time := by
    apply actual.congr_of_eventuallyEq
    filter_upwards with sample
    exact (source_mean seed M sample).symm
  exact original.unique (jet_hasDerivAt seed M 0 time)

theorem source_rate_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ‖mean (NativeWindowHistoryOseen.rateHistory seed M time)‖≤NativeForwardWindowJets.budget seed 1 := by
  change ‖(mean (NativeWindowHistoryOseen.rateHistory seed M time)).1‖≤_
  rw [source_rate]
  exact jet_bound seed M 1 time

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jet_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    jet seed M order (step.2.clockAdvance+time)=jet step.1 M order time := by
  unfold jet NativeForwardWindowEvolution.velocityJet
  exact congrArg (fun pair => read M pair.fst) (NativeForwardWindowJets.jet_next seed order step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanTime
