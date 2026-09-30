import H0mework.Versions.X.Fock.ReceivedStep.Residual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceReceivedConditionalStep

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def updatedSamples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (added key : Key) :
    SourceRationalWindowReadout.Samples (inventoryBound runtime.tick.next) ((maximumIndex runtime.tick.next).val + 1) :=
  completeSamples (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val
    (nextData runtime index (receiveState (inventoryBound runtime) index.val nonunit received key).1 (decide (key = added))
      (SourceRationalWindowReadout.decode (inventoryBound runtime) index.val (received key)))

def updatedModel (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (added key : Key) :
    SourceConditionalModel.NextModel runtime.tick.next :=
  SourceWindowPosterior.model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
    (SourceRationalWindowReadout.embed runtime.tick.next (maximumIndex runtime.tick.next) 0
      (updatedSamples runtime index nonunit received added key))

theorem realized_updated_model (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (received : Key → SourceRationalWindowReadout.Samples (inventoryBound runtime) (index.val + 1)) (added key : Key) :
    SourceConditionalVector.realizeModel runtime.tick.next (updatedModel runtime index nonunit received added key) =
      completeUpdatedValue runtime index nonunit received added key := by
  have evaluated := complete_roundtrip runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
    (nextData runtime index (receiveState (inventoryBound runtime) index.val nonunit received key).1 (decide (key = added))
      (SourceRationalWindowReadout.decode (inventoryBound runtime) index.val (received key)))
  simp only [Nat.add_zero] at evaluated
  have actual := SourceRationalWindowReadout.decoded_model runtime.tick.next (SourceMinimumSharedNext.next_nonunit runtime)
    (updatedSamples runtime index nonunit received added key)
  simp only [updatedSamples] at actual
  rw [evaluated] at actual
  exact actual.symm

theorem updated_model_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (nonunit : index.val ≠ 0)
    (read : Nat → Key) (key : Key) :
    updatedModel runtime index nonunit
      (fun value phase => SourceFiniteObserverCalculation.posteriorCalculate
        (inventoryBound runtime) (index.val + 1) 0 phase.val read value)
      (read runtime.tick.next.state) key = SourceConditionalNativeBirth.update runtime read key := by
  apply SourceActualImageStep.realize_injective runtime.tick.next
  rw [realized_updated_model, updated_value_source, SourceConditionalNativeBirth.update_is_next]
  rfl

end
end SourceReceivedConditionalStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
