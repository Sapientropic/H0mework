import H0mework.NavierStokes.WindowHistoryRecovery.Whole
import H0mework.NavierStokes.StressEvolutionUnfiltered.StressAlgebra
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceRecovery
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeEndpointVelocityCarrier (wholeVelocityCLM)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowTraceWholeHistory (history)
open NativeWindowHistoryWholeRecovery (retained)
open NativeForwardWindowPairingReadout (averageMeasure density)
open NativeCompleteStressCarrier (Space)
open NativeCompleteStressAction (FullSpace)
noncomputable section
variable {nu : Viscosity}

def fiber : wholePhysical →L[ℝ] wholePhysical →L[ℝ] Space :=
  NativeCompleteStressBilinear.mixedCLM.bilinearComp
    (wholeVelocityCLM.comp wholePhysical.subtypeL) (wholeVelocityCLM.comp wholePhysical.subtypeL)

def pairing : H →L[ℝ] H →L[ℝ] Space := fiber.lpPairing averageMeasure 2 2

def stress (v : H) : Space := pairing v v

theorem stress_integral (v : H) : stress v=∫ lag,fiber (v lag) (v lag) ∂averageMeasure :=
  fiber.lpPairing_eq_integral v v

theorem fiber_quadratic (v : wholePhysical) : fiber v v=NativeStressTimeAlgebra.quadratic v.1 := rfl

private theorem quadratic_continuous {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) :
    Continuous (fun v => B v v) := B.continuous.clm_apply continuous_id

theorem stress_continuous : Continuous stress := quadratic_continuous (E := H) pairing

theorem source_stress (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    stress (history seed time)=(NativeForwardWindowSource.source seed time).snd := by
  let read:=WithLp.sndL 2 ℝ NativeResolventCompactness.State Space
  have window:=NativeForwardWindowPairingReadout.linear_probability_integral read seed time
  change (NativeForwardWindowSource.source seed time).snd=
    ∫ lag,(NativeUnifiedCompleteSource.source seed (time-lag)).snd ∂averageMeasure at window
  have original:∀ᵐ sample ∂(volume : Measure ℝ),
      NativeStressTimeAlgebra.quadratic (NativeUnifiedCompleteSource.source seed sample).fst=
        (NativeUnifiedCompleteSource.source seed sample).snd := by
    filter_upwards [NativeUnifiedGlobalStressSource.stress_ae seed] with sample given
    apply NativeCompleteStressCarrier.read_injective
    change NativeCompleteStressCarrier.read (NativeCompleteStressBilinear.mixedCLM
      (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed sample).fst)
      (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed sample).fst))=_
    rw [NativeCompleteStressBilinear.mixedCLM_apply,NativeCompleteStressBilinear.mixed_read,
      NativeHigherTimeJets.mixedFlux_diagonal,NativeUnifiedCompleteSource.stress_read,
      NativeUnifiedCompleteSource.velocity_read,given]
  have shifted:∀ᵐ lag ∂averageMeasure,
      NativeStressTimeAlgebra.quadratic (NativeUnifiedCompleteSource.source seed (time-lag)).fst=
        (NativeUnifiedCompleteSource.source seed (time-lag)).snd :=
    (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le
      ((Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae original)
  rw [stress_integral,window]
  apply integral_congr_ae
  filter_upwards [NativeWindowTraceWholeHistory.history_ae seed time,shifted] with lag actual source
  rw [actual,fiber_quadratic]
  exact source

def read (v : H) : FullSpace := WithLp.toLp 2 ((mean v).1,stress v)

theorem read_continuous : Continuous read :=
  (WithLp.prod_continuous_toLp 2 NativeResolventCompactness.State Space).comp
    ((wholePhysical.subtypeL.comp mean).continuous.prodMk stress_continuous)

theorem source_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    read (history seed time)=NativeForwardWindowSource.source seed time := by
  apply (WithLp.equiv 2 (NativeResolventCompactness.State × Space)).injective
  exact Prod.ext (NativeWindowHistoryMeanProjection.source_mean seed time) (source_stress seed time)

def residual (v : H) : Space := stress v-NativeStressTimeAlgebra.quadratic (mean v).1

theorem residual_continuous : Continuous residual :=
  stress_continuous.sub (NativeStressTimeAlgebra.quadratic_continuous.comp (wholePhysical.subtypeL.comp mean).continuous)

theorem source_residual (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    residual (history seed time)=(NativeForwardWindowSource.source seed time).snd-
      NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst := by
  rw [residual,source_stress,NativeWindowHistoryMeanProjection.source_mean]

theorem source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) :
    Tendsto (fun M => read (retained seed M time)) atTop
      (𝓝 (NativeForwardWindowSource.source seed time)) := by
  have source:=read_continuous.tendsto (history seed time) |>.comp
    (NativeWindowHistoryWholeRecovery.source_tendsto seed time nonnegative)
  simpa only [Function.comp_def,source_read] using source

theorem residual_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0≤time) :
    Tendsto (fun M => residual (retained seed M time)) atTop
      (𝓝 ((NativeForwardWindowSource.source seed time).snd-
        NativeStressTimeAlgebra.quadratic (NativeForwardWindowSource.source seed time).fst)) := by
  have source:=residual_continuous.tendsto (history seed time) |>.comp
    (NativeWindowHistoryWholeRecovery.source_tendsto seed time nonnegative)
  simpa only [Function.comp_def,source_residual] using source

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem read_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    read (retained seed M (step.2.clockAdvance+time))=read (retained step.1 M time) :=
  congrArg read (NativeWindowHistoryWholeRecovery.retained_next seed M step generated time nonnegative)

theorem residual_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    residual (retained seed M (step.2.clockAdvance+time))=residual (retained step.1 M time) :=
  congrArg residual (NativeWindowHistoryWholeRecovery.retained_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCovarianceRecovery
