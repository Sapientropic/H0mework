import H0mework.Fock.ReceivedStep.Model

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem model_writeback (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (read : Nat → Key) (key : Key) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (updatedModel runtime index nonunit received (read runtime.tick.next.state) key) -
      comparisonResidual runtime index nonunit received read key = SourceConditionalNativePosterior.decoder runtime.tick.next read key := by
  rw [realized_updated_model, ← residual_equation]
  abel

theorem model_error (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => read actor.val)).support) :
    (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
        SourceConditionalVector.realizeModel runtime.tick.next
          (updatedModel runtime index nonunit received (read runtime.tick.next.state) key)‖ ^ 2) =
      (∑ actor : Actors runtime.tick.next, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next actor) -
          SourceConditionalNativePosterior.decoder runtime.tick.next read key‖ ^ 2) +
        ‖comparisonResidual runtime index nonunit received read key‖ ^ 2 := by
  rw [realized_updated_model]
  exact conditional_error runtime index nonunit received read key supported

theorem complete_feedback_strict (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (read : Nat → Key) :
    (∑ actor : Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalVector.realizeModel runtime.tick.next
          (updatedModel runtime index nonunit
            (fun value phase => SourceFiniteObserverCalculation.posteriorCalculate
              (inventoryBound runtime) (index.val + 1) 0 phase.val read value)
            (read runtime.tick.next.state) (read actor.val))‖ ^ 2) <
      ∑ actor : Actors runtime.tick.next,
        ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
          SourceConditionalNativePosterior.decoder runtime read (read actor.val)‖ ^ 2 := by
  have generated : (∑ actor : Actors runtime.tick.next,
      ‖SourceConditionalInventory.values (inventoryBound runtime.tick.next) actor -
        SourceConditionalVector.realizeModel runtime.tick.next
          (updatedModel runtime index nonunit
            (fun value phase => SourceFiniteObserverCalculation.posteriorCalculate
              (inventoryBound runtime) (index.val + 1) 0 phase.val read value)
            (read runtime.tick.next.state) (read actor.val))‖ ^ 2) = SourceConditionalNativeBirth.total runtime.tick.next read := by
    unfold SourceConditionalNativeBirth.total
    apply Finset.sum_congr rfl
    intro actor _
    rw [updated_model_source, SourceConditionalNativeBirth.update_is_next]
    rfl
  rw [generated]
  exact SourceConditionalNativeBirth.stale_strict runtime read

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
