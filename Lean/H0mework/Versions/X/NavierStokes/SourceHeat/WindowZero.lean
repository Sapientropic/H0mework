import H0mework.Versions.X.NavierStokes.SourceHeat.Zero

set_option autoImplicit false
open scoped Topology ENNReal NNReal ContDiff
namespace SaturationMonoid.NavierStokes.NativeZeroHeatWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressAction NativeCompleteHeatTransport NativeZeroHeat
noncomputable section
variable {nu : Viscosity}

theorem source_zero (seed : GeneratedWholeRestartCurrent nu) :
    NativeWindowHeatEvolution.source seed 0 = NativeForwardWindowSource.source seed := by
  funext time
  exact congrArg (fun action : FullSpace →L[ℝ] FullSpace => action (NativeForwardWindowSource.source seed time)) (fullHeat_zero nu)

theorem jet_zero (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) :
    NativeWindowHeatEvolution.jet seed 0 order = NativeForwardWindowJets.jet seed order := by
  funext time
  exact congrArg (fun action : FullSpace →L[ℝ] FullSpace => action (NativeForwardWindowJets.jet seed order time)) (fullHeat_zero nu)

theorem jet_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    Tendsto (fun lag : ℝ≥0 => NativeWindowHeatEvolution.jet seed lag order time) (𝓝 0)
      (𝓝 (NativeForwardWindowJets.jet seed order time)) :=
  fullHeat_tendsto nu (NativeForwardWindowJets.jet seed order time)

theorem source_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun lag : ℝ≥0 => NativeWindowHeatEvolution.source seed lag time) (𝓝 0)
      (𝓝 (NativeForwardWindowSource.source seed time)) :=
  fullHeat_tendsto nu (NativeForwardWindowSource.source seed time)

theorem jet_continuous (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) :
    Continuous (NativeForwardWindowJets.jet seed order) :=
  continuous_iff_continuousAt.mpr (fun time => (NativeForwardWindowJets.jet_hasDerivAt seed order time).continuousAt)

theorem jet_uniform_on_compact (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    {times : Set ℝ} (compact : IsCompact times) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => NativeWindowHeatEvolution.jet seed lag order)
      (NativeForwardWindowJets.jet seed order) (𝓝 0) times := by
  have generated := fullHeat_uniform_on_compact nu (compact.image (jet_continuous seed order))
  exact (generated.comp (NativeForwardWindowJets.jet seed order)).mono (subset_preimage_image _ _)

theorem source_uniform_on_compact (seed : GeneratedWholeRestartCurrent nu)
    {times : Set ℝ} (compact : IsCompact times) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => NativeWindowHeatEvolution.source seed lag)
      (NativeForwardWindowSource.source seed) (𝓝 0) times := by
  simpa only [NativeWindowHeatEvolution.jet_zero, NativeForwardWindowJets.jet_zero] using
    jet_uniform_on_compact seed 0 compact

theorem jet_momentum_tendsto (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    Tendsto (fun lag : ℝ≥0 => momentumCLM nu (NativeWindowHeatEvolution.jet seed lag order time)) (𝓝 0)
      (𝓝 (momentumCLM nu (NativeForwardWindowJets.jet seed order time))) :=
  momentum_tendsto nu (NativeForwardWindowJets.jet seed order time)

theorem source_residual_tendsto (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Tendsto (fun lag : ℝ≥0 => residualValue (NativeWindowHeatEvolution.source seed lag time)) (𝓝 0)
      (𝓝 (residualValue (NativeForwardWindowSource.source seed time))) :=
  residual_tendsto nu (NativeForwardWindowSource.source seed time)

theorem jet_momentum_uniform_on_compact (seed : GeneratedWholeRestartCurrent nu) (order : ℕ)
    {times : Set ℝ} (compact : IsCompact times) :
    TendstoUniformlyOn (fun lag : ℝ≥0 => fun time => momentumCLM nu (NativeWindowHeatEvolution.jet seed lag order time))
      (fun time => momentumCLM nu (NativeForwardWindowJets.jet seed order time)) (𝓝 0) times :=
  (momentumCLM nu).uniformContinuous.comp_tendstoUniformlyOn (jet_uniform_on_compact seed order compact)

theorem jet_uniform_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) :
    ∀ lag : ℝ≥0, ∀ time : ℝ, ‖NativeWindowHeatEvolution.jet seed lag order time‖ ≤ NativeForwardWindowJets.budget seed order :=
  fun lag time => NativeWindowHeatEvolution.jet_bound seed lag order time

theorem nativeRHS_tendsto (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) (time : ℝ) :
    Tendsto (fun lag : ℝ≥0 => NativeCompleteEvolution.nativeRHS nu modes (NativeWindowHeatEvolution.source seed lag time))
      (𝓝 0) (𝓝 (NativeCompleteEvolution.nativeRHS nu modes (NativeForwardWindowSource.source seed time))) :=
  (NativeCompleteActionOperator.nativeRHS_contDiff nu modes).continuous.continuousAt.tendsto.comp (source_tendsto seed time)

end
end SaturationMonoid.NavierStokes.NativeZeroHeatWindow
