import H0mework.Fock.HistoryConditional.MinimumWindowErrorEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumWindowError

open SourceCopyCurrentCoordinates (maximumIndex)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open SourceConditionalNativeObservers (generate)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem conditional_noise_cost (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next
        (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
        readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
          (SourceMinimumSharedNext.step runtime nonunit
            (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) +
              SourceMinimumSharedNext.native runtime))‖ ^ 2) =
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          readout runtime (maximumIndex runtime) nonunit 0
            (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) +
              SourceMinimumSharedNext.native runtime)‖ ^ 2) + 2 * (runtime.state : ℝ) + 3 := by
  rw [conditional_next_error runtime nonunit read key supported, conditional_error runtime nonunit read key supported,
    source_noise_energy]
  ring

end
end SourceMinimumWindowError
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
