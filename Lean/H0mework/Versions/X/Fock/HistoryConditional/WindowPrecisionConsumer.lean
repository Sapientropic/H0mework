import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionContinuous

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window)
open SourceMinimumWindowError (readout)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open SourceConditionalNativeObservers (generate)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem error_bound (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (target : SourceJointClockGraph.Carrier) (error : Window runtime index) :
    ‖target - readout runtime index nonunit steps (recordedPrefix runtime index steps (index.val + 1) target + error)‖ ^ 2 ≤
      ‖residual runtime index steps target‖ ^ 2 + gain runtime index nonunit steps * sampleEnergy runtime index error := by
  rw [SourceMinimumWindowError.error_energy]
  with_reducible exact add_le_add le_rfl (readout_bound runtime index nonunit steps error)

theorem conditional_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (error : Window runtime (maximumIndex runtime)) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        readout runtime (maximumIndex runtime) nonunit 0
          (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) + error)‖ ^ 2) ≤
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read key‖ ^ 2) +
        ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        gain runtime (maximumIndex runtime) nonunit 0 * sampleEnergy runtime (maximumIndex runtime) error := by
  rw [SourceMinimumWindowError.conditional_error runtime nonunit read key supported]
  with_reducible exact add_le_add le_rfl (readout_bound runtime (maximumIndex runtime) nonunit 0 error)

theorem conditional_next_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (error : Window runtime (maximumIndex runtime)) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next
        (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
        readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
          (SourceMinimumSharedNext.step runtime nonunit
            (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) + error))‖ ^ 2) ≤
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read key‖ ^ 2) +
        ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        nextGain runtime (maximumIndex runtime) nonunit 0 * sampleEnergy runtime (maximumIndex runtime) error := by
  rw [SourceMinimumWindowError.conditional_next_error runtime nonunit read key supported]
  with_reducible exact add_le_add le_rfl (action_readout_bound runtime (maximumIndex runtime) nonunit 0 error)

theorem effect_bound (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key) (error : Window runtime (maximumIndex runtime)) :
    ‖SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) -
      readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
        (SourceMinimumSharedNext.step runtime nonunit
          (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) + error))‖ ^ 2 ≤
      ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        nextGain runtime (maximumIndex runtime) nonunit 0 * sampleEnergy runtime (maximumIndex runtime) error := by
  rw [SourceMinimumWindowError.effect_error]
  with_reducible exact add_le_add le_rfl (action_readout_bound runtime (maximumIndex runtime) nonunit 0 error)

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
