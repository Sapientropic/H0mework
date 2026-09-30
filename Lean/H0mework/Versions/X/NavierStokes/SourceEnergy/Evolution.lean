import H0mework.Versions.X.NavierStokes.SourceEnergy.Content
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewEnergyEvolution

open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeCompleteStressAction NativeWindowHeatEvolution NativeViewEnergyContent NativeWordStressEnergy

noncomputable section

variable {nu : Viscosity}

def resolvedRate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  inner ℝ (velocityJet seed lag 0 time) (velocityJet seed lag 1 time)

def totalRate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  kineticRead (jet seed lag 1 time).snd / 2

def unresolvedRate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  totalRate seed lag time - resolvedRate seed lag time

theorem velocity_zero (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    velocityJet seed lag 0 time = (source seed lag time).fst := by
  rw [velocityJet, jet_zero]

theorem velocity_continuous (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (order : ℕ) :
    Continuous (velocityJet seed lag order) :=
  continuous_iff_continuousAt.mpr fun time => (velocityJet_hasDerivAt seed lag order time).continuousAt

theorem resolvedRate_continuous (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) :
    Continuous (resolvedRate seed lag) :=
  (velocity_continuous seed lag 0).inner (𝕜 := ℝ) (velocity_continuous seed lag 1)

theorem resolved_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    HasDerivAt (resolved seed lag) (resolvedRate seed lag time) time := by
  have actual := (velocityJet_hasDerivAt seed lag 0 time).norm_sq.div_const 2
  simpa only [Nat.zero_add, velocity_zero, resolved, resolvedRate, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using! actual

theorem resolved_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (first last : ℝ) :
    resolved seed lag last - resolved seed lag first = ∫ time in first..last, resolvedRate seed lag time :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => resolved_hasDerivAt seed lag time)
    ((resolvedRate_continuous seed lag).intervalIntegrable first last)).symm

theorem physical_energy_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (first last : ℝ) :
    ‖NativePhysicalFourier.realField (NativeEndpointVelocityCarrier.wholeVelocity (source seed lag last).fst)‖ ^ 2 / 2 -
      ‖NativePhysicalFourier.realField (NativeEndpointVelocityCarrier.wholeVelocity (source seed lag first).fst)‖ ^ 2 / 2 =
      ∫ time in first..last, resolvedRate seed lag time := by
  rw [← resolved_physical, ← resolved_physical]
  exact resolved_integral seed lag first last

def totalRead : FullSpace →L[ℝ] ℝ := kineticRead.comp
  (WithLp.sndL 2 ℝ
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointState
    NativeCompleteStressCarrier.Space)

theorem totalRate_continuous (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) :
    Continuous (totalRate seed lag) :=
  (totalRead.continuous.comp (continuous_iff_continuousAt.mpr
    fun time => (jet_hasDerivAt seed lag 1 time).continuousAt)).div_const 2

theorem total_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    HasDerivAt (total seed lag) (totalRate seed lag time) time := by
  have actual := (totalRead.hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed lag 0 time)).div_const 2
  simpa only [Nat.zero_add, jet_zero] using! actual

theorem total_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (first last : ℝ) :
    total seed lag last - total seed lag first = ∫ time in first..last, totalRate seed lag time :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => total_hasDerivAt seed lag time)
    ((totalRate_continuous seed lag).intervalIntegrable first last)).symm

theorem unresolved_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    HasDerivAt (unresolved seed lag) (unresolvedRate seed lag time) time := by
  have actual := (total_hasDerivAt seed lag time).sub (resolved_hasDerivAt seed lag time)
  convert! actual using 1
  funext sample
  change unresolved seed lag sample = total seed lag sample - resolved seed lag sample
  rw [split]
  ring

theorem unresolved_integral (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (first last : ℝ) :
    unresolved seed lag last - unresolved seed lag first = ∫ time in first..last, unresolvedRate seed lag time :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => unresolved_hasDerivAt seed lag time)
    (((totalRate_continuous seed lag).sub (resolvedRate_continuous seed lag)).intervalIntegrable first last)).symm

theorem momentum_rate (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) (valid : -1 < time) :
    NativeNegativeFourMomentum.embed (velocityJet seed lag 1 time) = momentumCLM nu (source seed lag time) := by
  simpa only [Nat.zero_add, jet_zero] using source_physical_word seed lag 0 time valid

end
end SaturationMonoid.NavierStokes.NativeViewEnergyEvolution
