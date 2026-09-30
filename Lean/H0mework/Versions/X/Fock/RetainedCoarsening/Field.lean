import H0mework.Versions.X.Fock.RetainedCoarsening.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (At value residual)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceObservationInvariantControls (parity)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open SourceConditionalModel (Actors dynamicRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def observationTable (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) :
    Field parity →₀ SourceJointClockGraph.Carrier :=
  (Finsupp.onFinset Finset.univ
    (fun key : ZMod 2 => value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock) key)
    (fun key _ => Finset.mem_univ key)).mapDomain (SourceConditionalNativeKeys.observed depth)

theorem observation_at (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) (key : ZMod 2) :
    observationTable runtime frame depth (SourceConditionalNativeKeys.observed depth key) =
      value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock) key := by
  rw [observationTable, Finsupp.mapDomain_apply (SourceConditionalNativeKeys.observed_injective depth), Finsupp.onFinset_apply]

theorem observation_dynamic (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) (actor : Actors runtime) :
    observationTable runtime frame depth (dynamicRead runtime depth actor) =
      value runtime (merge (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock) (actor.val : ZMod 2) := by
  rw [← SourceConditionalInventory.observation_original runtime depth, SourceConditionalNativeKeys.source_observed, observation_at]

theorem field_information (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat) :
    type_of% (SourceInformationReadback.model_decoder_cost runtime depth (observationTable runtime frame depth)) :=
  SourceInformationReadback.model_decoder_cost runtime depth _

theorem field_mean (runtime : LivingRuntimeState process) (depth : Nat) (actor : Actors runtime) :
    SourceConditionalVector.realizeModel runtime (SourceConditionalVector.dynamicEstimate runtime depth actor) =
      SourceConditionalNativePosterior.decoder runtime (fun index : Nat => (index : ZMod 2)) (actor.val : ZMod 2) := by
  have source : SourceConditionalNativeKeys.decoder runtime depth =
      SourceConditionalVector.vectorDecoder runtime (dynamicRead runtime depth) := by
    rw [SourceConditionalNativeKeys.decoder_original, SourceConditionalRationalStream.decoder_original,
      SourceConditionalWordStream.decoder_original, SourceConditionalFiniteStream.generated_read,
      SourceConditionalStream.generated_source, SourceConditionalInnovation.decoder_current]
  have original := congrFun source (dynamicRead runtime depth actor)
  rw [SourceConditionalVector.decoder_at, ← SourceConditionalInventory.observation_original runtime depth,
    SourceConditionalNativeKeys.source_observed, SourceConditionalNativePosterior.parity_decoder] at original
  exact original.symm

theorem field_balance (runtime : LivingRuntimeState process) (frame : At runtime (ℤ × ℤ)) (depth : Nat)
    (source : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) :
    SourceConditionalVector.dynamicError runtime depth (observationTable runtime frame depth) =
      SourceConditionalVector.dynamicVariance runtime depth +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖∑ key ∈ frame.keys,
          (weight (inventoryBound runtime) (maximumIndex runtime).val frame forgetClock (actor.val : ZMod 2) key : ℂ) •
            residual runtime frame key‖ ^ 2 := by
  have coarseSource := native_source _ _ frame (clockRead 0) forgetClock source keys
  have factor : forgetClock ∘ clockRead 0 = (fun index : Nat => (index : ZMod 2)) :=
    funext SourceConditionalNativeMerge.clock_factor
  rw [factor] at coarseSource
  rw [SourceConditionalVector.dynamic_error_decomposition]
  congr 1
  apply Finset.sum_congr rfl
  intro actor _
  rw [field_mean, observation_dynamic, ← residual_merge]
  rw [SourceRetainedReceiver.residual, SourceRetainedReceiver.model_source runtime _ _ _ coarseSource]
  exact congrArg (fun x : ℝ => (historyPMF (inventoryBound runtime) actor).toReal * x ^ 2)
    (norm_sub_rev _ _)

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
