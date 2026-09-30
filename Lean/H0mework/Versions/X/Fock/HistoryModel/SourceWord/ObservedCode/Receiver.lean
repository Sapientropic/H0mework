import H0mework.Versions.X.Fock.HistoryModel.SourceWord.ObservedCode.Source
import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordObservedCode

open SourceGeneratedActionWords SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceConditionalModel (Actors)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open scoped Classical
noncomputable section

theorem actual_nonunit : (maximumIndex (runtimeAt 3)).val ≠ 0 := by
  rw [SourceCopyCurrentCoordinates.maximum_index_val, inventory_bound, runtimeAt_state]
  decide

def actualKeys (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) : List (ZMod 2) :=
  (List.finRange (inventoryBound runtime + 1)).map
    (fun actor => readAt (inventoryBound runtime) word actor.val)

theorem actual_inventory (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    (actualKeys runtime word).toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime)
        (fun actor => readAt (inventoryBound runtime) word actor.val) := by
  ext key
  simp [actualKeys, SourceUniformFibreVariance.outputs]

def exactSamples (runtime : LivingRuntimeState process)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => readAt (inventoryBound runtime) word actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1) :=
  fun key phase => SourceFiniteObserverCalculation.posteriorCalculate
    (inventoryBound runtime) ((maximumIndex runtime).val + 1) 0 phase.val
    (readAt (inventoryBound runtime) word) key.val

theorem exact_budgets (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0
          (exactSamples runtime word key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
            ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime
              (readAt (inventoryBound runtime) word) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2 := by
  intro key
  have same : SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0
      (exactSamples runtime word key) =
      SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0
        ((maximumIndex runtime).val + 1)
        (SourceConditionalNativePosterior.decoder runtime
          (readAt (inventoryBound runtime) word) key.val) :=
    SourceRationalWindowReadout.posterior_samples runtime (maximumIndex runtime) 0
      (readAt (inventoryBound runtime) word) key.val
  rw [same, sub_self]
  simp only [SourceWindowPrecision.sampleEnergy, Pi.zero_apply, norm_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
  exact sq_pos_of_pos (SourcePosteriorStability.threshold_positive runtime)

def initial (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1))) :
    SourceRetainedReceiver.At runtime (ZMod 2) :=
  SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val
    nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => readAt (inventoryBound runtime) word actor.val))
    (exactSamples runtime word)

def table (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) : SourceCountedObservation.Table (ZMod 2) :=
  SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => readAt (inventoryBound runtime) word
      (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime)
      (maximumIndex runtime).val (actualKeys runtime word)
      (initial runtime nonunit word)) steps

theorem received (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) :
    SourceCountedObservation.Simulates (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val (table runtime nonunit word steps)
      (SourceRetainedReceiver.trajectory runtime (initial runtime nonunit word)
        (fun offset => readAt (inventoryBound runtime) word
          (inventoryBound runtime + offset + 1)) steps) := by
  simpa only [table, initial] using
    SourceCountedObservation.received_simulates runtime nonunit
      (readAt (inventoryBound runtime) word) (actualKeys runtime word)
      (actual_inventory runtime word) (exactSamples runtime word)
      (exact_budgets runtime nonunit word) steps

theorem counted_posterior (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (steps : Nat) (key : ZMod 2) :
    SourceCountedPosterior.restore (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (table runtime nonunit word steps) key =
        SourceConditionalNativeObservers.generate (readAt (inventoryBound runtime) word)
          (inventoryBound (runtime.advance steps)) key := by
  simpa only [table, initial] using
    SourceCountedPosterior.continued_source runtime nonunit
      (readAt (inventoryBound runtime) word) (actualKeys runtime word)
      (actual_inventory runtime word) (exactSamples runtime word)
      (exact_budgets runtime nonunit word) steps key

theorem observed_mass_received (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (word : List (Fock.Letter (inventoryBound runtime + 1)))
    (key : ZMod 2) :
    (postWordLaw runtime word key).toReal =
      ((SourceCountedPosterior.restore (inventoryBound runtime)
        (maximumIndex runtime).val
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
        (table runtime nonunit word 0) key).1 : ℝ) /
          (inventoryBound runtime + 1 : ℝ) := by
  have queryEq : sourceQuery runtime word =
      (fun actor : Actors runtime => readAt (inventoryBound runtime) word actor.val) := by
    funext actor
    exact source_query_read runtime word actor
  rw [post_word_law, queryEq,
    SourceUniformFibreVariance.observed_weight]
  have restored := counted_posterior runtime nonunit word 0 key
  simp only [LivingRuntimeState.advance] at restored
  rw [show (SourceCountedPosterior.restore (inventoryBound runtime)
      (maximumIndex runtime).val
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit 0)
      (table runtime nonunit word 0) key).1 =
        (SourceConditionalNativeObservers.generate (readAt (inventoryBound runtime) word)
          (inventoryBound runtime) key).1 from congrArg Prod.fst restored,
    SourceConditionalNativePosterior.count_fibre]

end
end SourceWordObservedCode
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
