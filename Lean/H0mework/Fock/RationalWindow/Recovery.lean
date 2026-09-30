import H0mework.Fock.RationalWindow.Decode

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

def weightAddress (bound stride : Nat) (nonunit : stride ≠ 0) (actor : Fin (bound + 1)) :
    Fin ((bound + 1) * (stride + 1)) :=
  ⟨actor.val + 1, by
    have wide : 1 < stride + 1 := by omega
    have capacity : bound + 1 < (bound + 1) * (stride + 1) := by nlinarith
    omega⟩

def recover (bound stride : Nat) (nonunit : stride ≠ 0) (samples : Samples bound (stride + 1)) : Fin (bound + 1) → ℚ :=
  fun actor => (decode bound stride samples).1 (weightAddress bound stride nonunit actor)

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def weightCoordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (actor : Fin (inventoryBound runtime + 1)) : Fin (cutoff runtime index 0 + 1) :=
  ⟨actor.val + 1, (weightAddress (inventoryBound runtime) index.val nonunit actor).isLt.trans_eq (by
    symm
    exact (SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime)).trans
      (by rw [SourceCopyProgram.scale_source]))⟩

theorem recovered_posterior (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    recover (inventoryBound runtime) index.val nonunit
      (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key) =
        (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 := by
  funext actor
  have source := decode_source runtime index nonunit 0
    (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key)
  rw [posterior_samples, SourceOperatorObservationAcquisition.decode_source] at source
  have value := congrArg (fun value : SourceCopyCurrentCoordinates.Coordinates runtime index 0 =>
    value.1 (weightCoordinate runtime index nonunit actor)) source
  change (recover (inventoryBound runtime) index.val nonunit
      (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key) actor : ℂ) =
    SourceCopyTimeModel.hilbert (SourceConditionalNativePosterior.decoder runtime read key) (actor.val + 1) at value
  rw [← SourceFiniteObserverCalculation.posterior_word runtime read key] at value
  change _ = SourceSuccessorBoundary.readWord (SourceConditionalRationalStream.embedWord
    (SourceConditionalNativeKeys.word (inventoryBound runtime)
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2)) (actor.val + 1) at value
  rw [SourceSuccessorBoundary.readWord_coordinate, SourceFiniteObserverCalculation.embed_at,
    SourceConditionalNativeKeys.word_coefficient] at value
  exact (Rat.cast_injective : Function.Injective (fun scalar : ℚ => (scalar : ℂ))) value

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
