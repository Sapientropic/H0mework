import H0mework.Versions.X.Fock.FiniteObserver.Posterior

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceConditionalModel (Actors)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem window_reconstruction (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) :
    SourceMinimumWindowError.readout runtime (maximumIndex runtime) nonunit 0
      (window runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) read key) +
      residual runtime (maximumIndex runtime) 0 (decoder runtime read key) = decoder runtime read key := by
  rw [window_source, SourceMinimumWindowError.readout_source]
  exact SourceCopyCurrentCoordinates.reconstruction runtime (maximumIndex runtime) 0 _

theorem window_model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) :
    SourceWindowPosterior.model runtime nonunit
      (window runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) read key) =
        SourceConditionalNativePosterior.model runtime read key := by
  rw [window_source]
  exact SourceWindowPosterior.model_source runtime nonunit read key

theorem window_effect (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) (error : SourceMinimumSharedNext.Window runtime) :
    ‖SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) -
      SourceMinimumWindowError.readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
        (SourceMinimumSharedNext.step runtime nonunit
          (window runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) read key + error))‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        ‖SourceJointClockGraph.action (SourceMinimumWindowError.readout runtime (maximumIndex runtime) nonunit 0 error)‖ ^ 2 := by
  rw [window_source]
  with_reducible exact SourceMinimumWindowError.effect_error runtime nonunit read key error

theorem window_next_support (runtime : LivingRuntimeState process) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => read actor.val)).support) :
    SourcePosteriorStability.restoredSupport runtime.tick.next
      (SourceWindowPosterior.model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
        (window runtime.tick.next (maximumIndex runtime.tick.next) 0 ((maximumIndex runtime.tick.next).val + 1) read key)) =
      SourceUniformFibreVariance.fibre (inventoryBound runtime.tick.next) (fun actor => read actor.val) key := by
  rw [window_source]
  exact SourceWindowPosterior.exact_support runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime) read key supported

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
