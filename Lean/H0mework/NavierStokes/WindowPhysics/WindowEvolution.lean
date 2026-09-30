import H0mework.NavierStokes.WindowPhysics.WindowJets
import H0mework.NavierStokes.WindowPhysics.WindowWrite
import H0mework.NavierStokes.NativeAction.Operator

set_option autoImplicit false
open scoped Topology ENNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeForwardWindowEvolution

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeForwardWindowSource NativeForwardWindowJets
open NativeForwardWindowWrite

noncomputable section

variable {nu : Viscosity}

def velocityJet (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    WholeRestartVelocityEndpointState := (jet seed order time).fst

def velocityRead : FullSpace →L[ℝ] WholeRestartVelocityEndpointState :=
  WithLp.fstL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space

theorem velocityJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    HasDerivAt (velocityJet seed order) (velocityJet seed (order + 1) time) time :=
  velocityRead.hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed order time)

theorem velocityJet_bound (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    ‖velocityJet seed order time‖ ≤ budget seed order :=
  (WithLp.norm_fst_le _ (jet seed order time)).trans (jet_bound seed order time)

theorem source_physical_rate (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 < time) :
    NativeNegativeFourMomentum.embed (velocityJet seed 1 time) = momentumCLM nu (source seed time) := by
  have lifted := NativeNegativeFourMomentum.embed.hasFDerivAt.comp_hasDerivAt time
    (velocityJet_hasDerivAt seed 0 time)
  have original := state_hasDerivAt seed time valid
  have represented : HasDerivAt (state seed) (NativeNegativeFourMomentum.embed (velocityJet seed 1 time)) time := by
    apply lifted.congr_of_eventuallyEq
    filter_upwards with sample
    rw [state_embedded]
    change _ = NativeNegativeFourMomentum.embed (jet seed 0 sample).fst
    rw [jet_zero]
  exact represented.unique original

theorem source_physical_word (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (valid : -1 < time) :
    NativeNegativeFourMomentum.embed (velocityJet seed (order + 1) time) = momentumCLM nu (jet seed order time) := by
  induction order generalizing time with
  | zero => simpa only [Nat.zero_add, jet_zero] using source_physical_rate seed time valid
  | succ order previous =>
      have physical := NativeNegativeFourMomentum.embed.hasFDerivAt.comp_hasDerivAt time
        (velocityJet_hasDerivAt seed (order + 1) time)
      have action := (momentumCLM nu).hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed order time)
      have matched := action.congr_of_eventuallyEq (by
        filter_upwards [eventually_gt_nhds valid] with sample inside
        exact previous sample inside)
      exact physical.unique matched

theorem source_action_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ) :
    HasDerivAt (fun sample => momentumCLM nu (jet seed order sample))
      (momentumCLM nu (jet seed (order + 1) time)) time :=
  (momentumCLM nu).hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed order time)

theorem complete_native_rate (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector)
    (time : ℝ) (valid : -1 < time) :
    HasDerivAt (fun sample => NativeCompleteFilteredWrite.readCLM modes (state seed sample))
      (NativeCompleteEvolution.nativeRHS nu modes (source seed time)) time := by
  have physical := (NativeCompleteFilteredWrite.readCLM modes).hasFDerivAt.comp_hasDerivAt time
    (state_hasDerivAt seed time valid)
  simpa only [NativeCompleteActionOperator.nativeRHS_eq_actionCLM,
    NativeCompleteActionOperator.actionCLM, ContinuousLinearMap.comp_apply] using! physical

end
end SaturationMonoid.NavierStokes.NativeForwardWindowEvolution
