import H0mework.Versions.X.Fock.HistoryModel.SourceWord.Minimal
import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWordPrecisionGeneric

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors NextModel nextRead)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceGeneratedActionWords
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def fineTable (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1)) (steps : Nat) :
    SourceCountedObservation.Table (ℤ × ℤ) :=
  let initial := SourceRetainedReceiver.start (inventoryBound runtime)
    (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)) samples
  SourceCountedObservation.run (inventoryBound runtime)
    (fun offset => clockRead 0 (inventoryBound runtime + offset + 1))
    (SourceCountedObservation.fromInventory (inventoryBound runtime)
      (maximumIndex runtime).val keys initial) steps

/-- One initial source budget pays the complete fine counted Model at every later step. -/
theorem continued_model (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime)
            0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) (key : ℤ × ℤ) :
    SourceCountedPosterior.model (runtime.advance steps)
      (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
      (fineTable runtime nonunit keys samples steps) key =
    SourceConditionalNativePosterior.model (runtime.advance steps) (clockRead 0) key := by
  simpa only [fineTable] using SourceCountedPosterior.continued_model runtime nonunit
    (clockRead 0) keys inventory samples budgets steps key

/-- The original counted fine Model is an exact anchor; perturbation is a consumer condition. -/
theorem word_precision (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime)
            0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat)
    (word : List (Fock.Letter (inventoryBound (runtime.advance steps) + 1)))
    (actor : Actors (runtime.advance steps))
    (candidate : NextModel (runtime.advance steps))
    (small : ‖SourceConditionalVector.realizeModel (runtime.advance steps) candidate -
      SourceConditionalVector.realizeModel (runtime.advance steps)
        (SourceCountedPosterior.model (runtime.advance steps)
          (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
          (fineTable runtime nonunit keys samples steps) (clockRead 0 actor.val))‖ <
      SourcePosteriorStability.threshold (runtime.advance steps)) :
    SourcePosteriorStability.restoredSupport (runtime.advance steps) candidate =
      SourceUniformFibreVariance.fibre (inventoryBound (runtime.advance steps))
        (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word)
        (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word actor) := by
  have anchor := continued_model runtime nonunit keys inventory samples budgets steps
    (clockRead 0 actor.val)
  have supported : clockRead 0 actor.val ∈
      ((historyPMF (inventoryBound (runtime.advance steps))).map
        (fun index : Actors (runtime.advance steps) => clockRead 0 index.val)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr
      ⟨actor, SourceUniformFibreVariance.source_positive _ _, rfl⟩
  have bounded : ‖SourceConditionalVector.realizeModel (runtime.advance steps) candidate -
      SourceConditionalNativePosterior.decoder (runtime.advance steps)
        (clockRead 0) (clockRead 0 actor.val)‖ <
      SourcePosteriorStability.threshold (runtime.advance steps) := by
    rw [SourceConditionalNativePosterior.decoder, ← anchor]
    exact small
  have restored := SourceConditionalNativePosterior.support_restored (runtime.advance steps)
    (clockRead 0) (clockRead 0 actor.val) supported candidate bounded
  rw [restored]
  ext index
  rw [SourceUniformFibreVariance.fibre_mem, SourceUniformFibreVariance.fibre_mem]
  exact ⟨fun same => congrArg (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word)
      (Fin.ext (SourceConditionalNativeObservers.clock_injective 0 same)),
    fun same => congrArg (fun point : Actors (runtime.advance steps) => clockRead 0 point.val)
      ((SourceWordMinimalCode.wordEquiv (runtime.advance steps) word).injective same)⟩

theorem word_singleton (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime)
            0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat)
    (word : List (Fock.Letter (inventoryBound (runtime.advance steps) + 1)))
    (actor : Actors (runtime.advance steps)) :
    SourcePosteriorStability.restoredSupport (runtime.advance steps)
      (SourceCountedPosterior.model (runtime.advance steps)
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
        (fineTable runtime nonunit keys samples steps) (clockRead 0 actor.val)) =
      SourceUniformFibreVariance.fibre (inventoryBound (runtime.advance steps))
        (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word)
        (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word actor) := by
  apply word_precision runtime nonunit keys inventory samples budgets steps word actor
  simpa only [sub_self, norm_zero] using
    SourcePosteriorStability.threshold_positive (runtime.advance steps)

/-- A retained word code reaches the old physical G decoder, also under a small candidate error. -/
theorem word_g_reader (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime)
            0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat)
    (word : List (Fock.Letter (inventoryBound (runtime.advance steps) + 1)))
    (actor codeActor : Actors (runtime.advance steps))
    (candidate : NextModel (runtime.advance steps))
    (small : ‖SourceConditionalVector.realizeModel (runtime.advance steps) candidate -
      SourceConditionalVector.realizeModel (runtime.advance steps)
        (SourceCountedPosterior.model (runtime.advance steps)
          (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
          (fineTable runtime nonunit keys samples steps) (clockRead 0 actor.val))‖ <
      SourcePosteriorStability.threshold (runtime.advance steps))
    (seen : codeActor ∈ SourcePosteriorStability.restoredSupport
      (runtime.advance steps) candidate) :
    SourceWordMinimalCode.decode (runtime.advance steps) word
        (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word codeActor) =
      SourceCompiledGWord.image (runtime.advance steps)
        (inventoryBound (runtime.advance steps) + 1) word actor := by
  rw [word_precision runtime nonunit keys inventory samples budgets steps word actor candidate small,
    SourceUniformFibreVariance.fibre_mem] at seen
  have same := (SourceWordMinimalCode.wordEquiv (runtime.advance steps) word).injective seen
  subst codeActor
  exact SourceWordMinimalCode.decode_actual (runtime.advance steps) word actor

/-- The original actor posterior has a quantitative squared-error budget around the counted anchor. -/
theorem posterior_weight_budget (runtime : LivingRuntimeState process)
    (nonunit : (maximumIndex runtime).val ≠ 0)
    (keys : List (ℤ × ℤ))
    (inventory : keys.toFinset = SourceUniformFibreVariance.outputs
      (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime)
          ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime)
            0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2)
    (steps : Nat) (actor : Actors (runtime.advance steps))
    (candidate : NextModel (runtime.advance steps)) :
    (∑ index : Actors (runtime.advance steps),
      |(SourcePosteriorReadback.readWeight (runtime.advance steps) candidate index).toReal -
        (PMF.pure actor index).toReal| ^ 2) ≤
    ‖SourceConditionalVector.realizeModel (runtime.advance steps) candidate -
      SourceConditionalVector.realizeModel (runtime.advance steps)
        (SourceCountedPosterior.model (runtime.advance steps)
          (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
          (fineTable runtime nonunit keys samples steps) (clockRead 0 actor.val))‖ ^ 2 := by
  have anchorExact :
      SourceCountedPosterior.model (runtime.advance steps)
        (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps)
        (fineTable runtime nonunit keys samples steps) (clockRead 0 actor.val) =
      nextRead (runtime.advance steps) actor := by
    rw [continued_model runtime nonunit keys inventory samples budgets steps (clockRead 0 actor.val),
      ← SourceConditionalNativeObservers.full_source]
    exact SourceConditionalNativeObservers.model_recovers (runtime.advance steps) actor
  rw [anchorExact]
  simpa only [SourcePosteriorReadback.source_weight] using
    (SourcePosteriorStability.weights_inventory (runtime.advance steps)
      candidate (nextRead (runtime.advance steps) actor))

end
end SourceWordPrecisionGeneric
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
