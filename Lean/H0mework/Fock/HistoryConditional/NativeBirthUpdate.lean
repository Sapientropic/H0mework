import H0mework.Fock.HistoryConditional.NativeBirthSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeBirth

open SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (NextModel)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def update (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) : NextModel runtime.tick.next :=
  let previous := SourceActualImageStep.retainModel runtime (SourceConditionalNativePosterior.model runtime read value)
  if value = read (inventoryBound runtime + 1) then
    previous + ((((SourceConditionalNativeObservers.generate read (inventoryBound runtime) value).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) •
      ((SourceActualImageStep.birth runtime).val - previous)
  else previous

theorem decoder_next (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) :
    SourceConditionalNativePosterior.decoder runtime.tick.next read value =
      if value = read (inventoryBound runtime + 1) then
        SourceConditionalNativePosterior.decoder runtime read value +
          ((((SourceConditionalNativeObservers.generate read (inventoryBound runtime) value).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) •
            (SourceConditionalInventory.born (inventoryBound runtime) - SourceConditionalNativePosterior.decoder runtime read value)
      else SourceConditionalNativePosterior.decoder runtime read value := by
  rw [decoder_word, SourceActualImageStep.next_bound, word_next]
  by_cases selected : value = read (inventoryBound runtime + 1)
  · rw [if_pos selected, if_pos selected, map_add, map_smul, ← algebraMap_smul ℂ, map_add, map_smul,
      map_sub, map_sub, SourceConditionalRationalStream.born_embed, SourceConditionalWordStream.born_read,
      ← decoder_word]
    simp only [map_inv₀, map_natCast, Rat.cast_natCast]
  · rw [if_neg selected, if_neg selected, ← decoder_word]

theorem update_is_next (runtime : LivingRuntimeState process) (read : Nat → Key) :
    update runtime read = SourceConditionalNativePosterior.model runtime.tick.next read := by
  funext value
  apply SourceActualImageStep.realize_injective runtime.tick.next
  change _ = SourceConditionalNativePosterior.decoder runtime.tick.next read value
  rw [decoder_next]
  by_cases selected : value = read (inventoryBound runtime + 1)
  · simp only [update, if_pos selected, map_add, map_smul, map_sub, retained_model,
      SourceConditionalModelUpdate.birth_realization]
  · simp only [update, if_neg selected, retained_model]

end
end SourceConditionalNativeBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
