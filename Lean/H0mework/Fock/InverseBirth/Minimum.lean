import H0mework.Fock.InverseBirth.Update

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimalBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def increment (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) : ℝ :=
  let count := (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1
  ‖SourceGWordInverse.residual depth word (SourceConditionalInventory.born (inventoryBound runtime))‖ ^ 2 +
    (count : ℝ) / (count + 1) *
      ‖project depth word (SourceConditionalInventory.born (inventoryBound runtime)) -
        decoder runtime depth word read (read (inventoryBound runtime + 1))‖ ^ 2

theorem born_error (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    ‖SourceConditionalInventory.born (inventoryBound runtime) -
      decoder runtime.tick.next depth word read (read (inventoryBound runtime + 1))‖ ^ 2 =
    ‖SourceGWordInverse.residual depth word (SourceConditionalInventory.born (inventoryBound runtime))‖ ^ 2 +
      ‖project depth word (SourceConditionalInventory.born (inventoryBound runtime)) -
        decoder runtime.tick.next depth word read (read (inventoryBound runtime + 1))‖ ^ 2 := by
  change ‖SourceConditionalInventory.born (inventoryBound runtime) - SourceCompiledGWord.effect depth word
    (SourceGWordInverse.recover depth word
      (SourceConditionalNativePosterior.decoder runtime.tick.next read (read (inventoryBound runtime + 1)) ))‖ ^ 2 = _
  rw [SourceInverseDistributionOptimal.error_decomposition, map_sub]
  rfl

theorem minimum_update (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    total runtime.tick.next depth word read = total runtime depth word read + increment runtime depth word read := by
  rw [minimum_difference, born_error, decoder_next, if_pos rfl]
  simp only [Rat.cast_natCast]
  have energy := SourceConditionalNativeBirth.mean_update_energy
    (SourceConditionalNativeObservers.generate read (inventoryBound runtime) (read (inventoryBound runtime + 1))).1
    (decoder runtime depth word read (read (inventoryBound runtime + 1)))
    (project depth word (SourceConditionalInventory.born (inventoryBound runtime)))
  dsimp only [increment]
  linarith only [energy]

end
end SourceInverseDistributionOptimalBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
