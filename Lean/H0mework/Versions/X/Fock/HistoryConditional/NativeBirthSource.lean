import H0mework.Versions.X.Fock.HistoryConditional.InformationLossConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem decoder_word (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) :
    SourceConditionalNativePosterior.decoder runtime read value =
      SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord
        (SourceConditionalNativeKeys.word (inventoryBound runtime)
          (SourceConditionalNativeObservers.generate read (inventoryBound runtime) value).2)) := by
  have paid := congrFun (SourceConditionalMergeLoss.decoder_original runtime read id) value
  simpa only [SourceConditionalMergeLoss.decoder, SourceConditionalNativeMerge.merged_generated, Function.id_comp] using paid.symm

theorem word_next (read : Nat → Key) (bound : Nat) (value : Key) :
    SourceConditionalNativeKeys.word (bound + 1) (SourceConditionalNativeObservers.generate read (bound + 1) value).2 =
      if value = read (bound + 1) then
        SourceConditionalNativeKeys.word bound (SourceConditionalNativeObservers.generate read bound value).2 +
          (((SourceConditionalNativeObservers.generate read bound value).1 + 1 : Nat) : ℚ)⁻¹ •
            (SourceConditionalRationalStream.bornWord bound -
              SourceConditionalNativeKeys.word bound (SourceConditionalNativeObservers.generate read bound value).2)
      else SourceConditionalNativeKeys.word bound (SourceConditionalNativeObservers.generate read bound value).2 := by
  rw [SourceConditionalNativeObservers.generated_next]
  by_cases selected : value = read (bound + 1)
  · simp only [SourceConditionalNativeObservers.advance, if_pos selected, SourceConditionalNativeKeys.word_updated]
  · simp only [SourceConditionalNativeObservers.advance, if_neg selected, SourceConditionalNativeKeys.word_retained]

theorem retained_model (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (SourceActualImageStep.retainModel runtime (SourceConditionalNativePosterior.model runtime read value)) =
        SourceConditionalNativePosterior.decoder runtime read value := by
  have same : SourceConditionalNativePosterior.model runtime read value =
      SourceConditionalModelUpdate.modelDecoder runtime (fun actor => read actor.val) value := by
    apply SourceActualImageStep.realize_injective runtime
    change SourceConditionalNativePosterior.decoder runtime read value = _
    rw [SourceConditionalModelUpdate.model_decoder_realization, SourceConditionalNativePosterior.decoder_original]
  rw [same, SourceConditionalModelUpdate.retained_decoder, SourceConditionalNativePosterior.decoder_original]

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
