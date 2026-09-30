import H0mework.Fock.InverseOptimal.Consumer
import H0mework.Fock.HistoryConditional.NativeBirthInnovation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseDistributionOptimalBirth

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def project (depth : Nat) (word : List (Fock.Letter depth)) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (SourceCompiledGWord.effect depth word).comp (SourceGWordInverse.recover depth word)

def decoder {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) : SourceJointClockGraph.Carrier :=
  project depth word (SourceConditionalNativePosterior.decoder runtime read key)

def total {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) : ℝ :=
  ∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
    decoder runtime depth word read (read actor.val)‖ ^ 2

theorem inverse_next {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime.tick.next read key) =
      if key = read (inventoryBound runtime + 1) then
        SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key) +
          ((((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) •
            (SourceGWordInverse.recover depth word (SourceConditionalInventory.born (inventoryBound runtime)) -
              SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key))
      else SourceGWordInverse.recover depth word (SourceConditionalNativePosterior.decoder runtime read key) := by
  rw [SourceConditionalNativeBirth.decoder_next]
  by_cases selected : key = read (inventoryBound runtime + 1)
  · simp only [if_pos selected, map_add, map_smul, map_sub]
  · simp only [if_neg selected]

theorem decoder_next {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    decoder runtime.tick.next depth word read key =
      if key = read (inventoryBound runtime + 1) then
        decoder runtime depth word read key +
          ((((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).1 + 1 : Nat) : ℚ)⁻¹ : ℂ) •
            (project depth word (SourceConditionalInventory.born (inventoryBound runtime)) - decoder runtime depth word read key)
      else decoder runtime depth word read key := by
  simp only [decoder, SourceConditionalNativeBirth.decoder_next]
  by_cases selected : key = read (inventoryBound runtime + 1)
  · simp only [if_pos selected, map_add, map_smul, map_sub]
  · simp only [if_neg selected]

theorem total_source {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) :
    total runtime depth word read = SourceConditionalNativeBirth.total runtime read +
      ∑ actor : Actors runtime, ‖SourceGWordInverse.residual depth word
        (SourceConditionalNativePosterior.decoder runtime read (read actor.val))‖ ^ 2 := by
  exact SourceConditionalNativeBirth.total_decomposition runtime read (decoder runtime depth word read)

theorem total_decomposition {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (guess : Key → SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
      SourceCompiledGWord.effect depth word (guess (read actor.val))‖ ^ 2) =
    total runtime depth word read + ∑ actor : Actors runtime,
      ‖decoder runtime depth word read (read actor.val) - SourceCompiledGWord.effect depth word (guess (read actor.val))‖ ^ 2 := by
  rw [SourceConditionalNativeBirth.total_decomposition runtime read (fun key => SourceCompiledGWord.effect depth word (guess key))]
  conv_lhs => simp only [SourceInverseDistributionOptimal.error_decomposition]
  rw [Finset.sum_add_distrib, ← add_assoc, ← total_source]
  congr 1
  apply Finset.sum_congr rfl
  intro actor _
  rw [map_sub]
  rfl

end
end SourceInverseDistributionOptimalBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
