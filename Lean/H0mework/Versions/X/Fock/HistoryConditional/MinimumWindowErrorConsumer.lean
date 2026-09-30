import H0mework.Versions.X.Fock.HistoryConditional.MinimumWindowErrorNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumWindowError

open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open SourceConditionalNativeObservers (generate)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem conditional_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (error : Window runtime (maximumIndex runtime)) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        readout runtime (maximumIndex runtime) nonunit 0
          (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) + error)‖ ^ 2) =
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read key‖ ^ 2) +
        ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        ‖readout runtime (maximumIndex runtime) nonunit 0 error‖ ^ 2 := by
  rw [SourceConditionalNativePosterior.error_decomposition runtime read key supported, error_energy]
  exact (add_assoc _ _ _).symm

theorem effect_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) (error : Window runtime (maximumIndex runtime)) :
    ‖SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) -
      readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
        (SourceMinimumSharedNext.step runtime nonunit
          (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) + error))‖ ^ 2 =
      ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        ‖SourceJointClockGraph.action (readout runtime (maximumIndex runtime) nonunit 0 error)‖ ^ 2 := by
  have paid := step_error runtime nonunit (decoder runtime read key) error
  rw [← SourceConditionalNativePosterior.effect_realization runtime read key] at paid
  with_reducible exact paid

theorem source_noise_energy (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0) :
    ‖SourceJointClockGraph.action
      (readout runtime (maximumIndex runtime) nonunit 0 (SourceMinimumSharedNext.native runtime))‖ ^ 2 =
      ‖readout runtime (maximumIndex runtime) nonunit 0 (SourceMinimumSharedNext.native runtime)‖ ^ 2 +
        2 * (runtime.state : ℝ) + 3 := by
  rw [readout, LinearMap.comp_apply, SourceMinimumSharedNext.native,
    SourceOperatorObservationAcquisition.decode_source, SourceCopyNativeSharedUpdate.source_realize,
    SourceJointClockGraph.action_energy, SourceConditionalVector.native_form]
  change _ + ‖(1 : ℂ)‖ ^ 2 + 2 * (inner ℂ ((runtime.state : ℂ) + 1) 1).re = _
  norm_num [inner]
  ring

end
end SourceMinimumWindowError
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
