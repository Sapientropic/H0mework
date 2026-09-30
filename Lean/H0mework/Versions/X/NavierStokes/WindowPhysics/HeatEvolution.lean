import H0mework.Versions.X.NavierStokes.WindowPhysics.HeatCarrier
import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowEvolution

set_option autoImplicit false
open scoped Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowHeatEvolution

open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressAction NativeUnifiedHeatAction
open NativeCompleteHeatTransport

noncomputable section

variable {nu : Viscosity}

def source (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : FullSpace :=
  fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)

def jet (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (time : ℝ) : FullSpace :=
  fullHeatCLM nu lag (NativeForwardWindowJets.jet seed order time)

theorem jet_zero (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) : jet seed lag 0 = source seed lag := by
  funext time
  rw [jet, NativeForwardWindowJets.jet_zero]
  rfl

theorem jet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (time : ℝ) :
    HasDerivAt (jet seed lag order) (jet seed lag (order + 1) time) time :=
  (fullHeatCLM nu lag).hasFDerivAt.comp_hasDerivAt time (NativeForwardWindowJets.jet_hasDerivAt seed order time)

theorem jet_bound (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (time : ℝ) :
    ‖jet seed lag order time‖ ≤ NativeForwardWindowJets.budget seed order :=
  (fullHeat_bound nu lag _).trans (NativeForwardWindowJets.jet_bound seed order time)

theorem source_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) : ContDiff ℝ ∞ (source seed lag) :=
  (fullHeatCLM nu lag).contDiff.comp (NativeForwardWindowSource.source_smooth seed)

def velocityJet (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (time : ℝ) :
    WholeRestartVelocityEndpointState := (jet seed lag order time).fst

theorem velocityJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (time : ℝ) :
    HasDerivAt (velocityJet seed lag order) (velocityJet seed lag (order + 1) time) time :=
  NativeForwardWindowEvolution.velocityRead.hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed lag order time)

theorem source_physical_word (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) (time : ℝ)
    (valid : -1 < time) :
    NativeNegativeFourMomentum.embed (velocityJet seed lag (order + 1) time) = momentumCLM nu (jet seed lag order time) := by
  rw [jet, fullHeatCLM_apply, momentum_heat, ← NativeForwardWindowEvolution.source_physical_word seed order time valid,
    heatCLM_embed]
  rfl

def state (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : WholeRestartVelocityEndpointState :=
  heatCLM nu lag (NativeForwardWindowWrite.state seed time)

theorem state_embedded (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    state seed lag time = NativeNegativeFourMomentum.embed (source seed lag time).fst := by
  rw [state, NativeForwardWindowWrite.state_embedded, heatCLM_embed]
  rfl

theorem state_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) (valid : -1 < time) :
    HasDerivAt (state seed lag) (momentumCLM nu (source seed lag time)) time := by
  have actual := (heatCLM nu lag).hasFDerivAt.comp_hasDerivAt time
    (NativeForwardWindowWrite.state_hasDerivAt seed time valid)
  simpa only [source, fullHeatCLM_apply, momentum_heat] using! actual

theorem state_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (a b : ℝ)
    (a_valid : -1 ≤ a) (b_valid : -1 ≤ b) :
    state seed lag b - state seed lag a = ∫ time in a..b, momentumCLM nu (source seed lag time) := by
  have actual := congrArg (heatCLM nu lag) (NativeForwardWindowWrite.state_integral seed a b a_valid b_valid)
  rw [map_sub, ← (heatCLM nu lag).intervalIntegral_comp_comm
    ((NativeForwardWindowWrite.momentum_continuous seed).intervalIntegrable a b)] at actual
  simpa only [source, fullHeatCLM_apply, momentum_heat] using! actual

theorem source_next (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    source seed lag (response.2.clockAdvance + time) = source response.1 lag time := by
  rw [source, source, NativeForwardWindowSource.source_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHeatEvolution
