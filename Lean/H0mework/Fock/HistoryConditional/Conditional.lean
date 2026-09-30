import H0mework.Fock.HistoryConditional.GWordInverseResidual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordInverse

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyTimeModel
open SourceConditionalModel (Actors)
open SourceConditionalInventory (values)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem decoder_moments (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    let p := SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => read actor.val) key supported
    recover depth word (SourceConditionalNativePosterior.decoder runtime read key) =
      SourceVectorMoment.mean p (fun actor : Actors runtime => SourceJointClockGraph.read (SourceClockComplex.ofNative
        (SourceCompiledWordOperator.recover depth word (SourceOperationNative.point ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next)))) +
      SourceVectorMoment.mean p (fun actor : Actors runtime => correction depth word
        (SourceOperationNative.point ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next)) := by
  dsimp only
  rw [SourceConditionalNativePosterior.decoder_mean _ _ _ supported,
    ← show values (inventoryBound runtime) = (fun actor => SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime actor)) from
      funext (SourceConditionalInventory.values_original runtime)]
  simp only [SourceVectorMoment.mean, map_sum, map_smul, values, SourceCopyNativeModelStep.sourceValue,
    recovery_native_moments, smul_add, Finset.sum_add_distrib]

theorem decoder_residual (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth))
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    let p := SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
      (fun actor : Actors runtime => read actor.val) key supported
    let remainder := fun actor : Actors runtime => SourceJointClockGraph.read (SourceClockComplex.ofNative
      (SourceCompiledWordOperator.residual depth word (SourceOperationNative.point ((history runtimeSeed (inventoryBound runtime)).stageAt actor).next)))
    residual depth word (SourceConditionalNativePosterior.decoder runtime read key) +
      SourceVectorMoment.mean p (fun actor => SourceCopyGraph.axes (mass (remainder actor)) (SourceJointClockGraph.clock (remainder actor))) =
        SourceVectorMoment.mean p remainder := by
  dsimp only
  rw [SourceConditionalNativePosterior.decoder_mean _ _ _ supported,
    ← show values (inventoryBound runtime) = (fun actor => SourceConditionalVector.realizeModel runtime (SourceConditionalModel.nextRead runtime actor)) from
      funext (SourceConditionalInventory.values_original runtime)]
  simp only [SourceVectorMoment.mean, map_sum, map_smul, values, SourceCopyNativeModelStep.sourceValue,
    ← Finset.sum_add_distrib, ← smul_add, residual_native_moments]

end
end SourceGWordInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
