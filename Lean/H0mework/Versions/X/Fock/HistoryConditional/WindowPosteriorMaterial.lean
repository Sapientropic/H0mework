import H0mework.Versions.X.Fock.HistoryConditional.WindowPosteriorNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPosterior

open SourceCopyCurrentCoordinates (maximumIndex)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  (∀ nonunit : (maximumIndex runtime).val ≠ 0,
    (∀ actor : Actors runtime, type_of% (actor_tail_zero runtime nonunit actor)) ∧
    ∀ key : ZMod 2,
      type_of% (decoder_tail_zero runtime nonunit (fun index : Nat => (index : ZMod 2)) key) ∧
      type_of% (model_source runtime nonunit (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support,
        type_of% (exact_support runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported) ∧
        ∀ samples : Window runtime (maximumIndex runtime),
          type_of% (model_realization runtime nonunit samples) ∧
          type_of% (bias_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key samples) ∧
          ∀ budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
            SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
              (samples - recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
                (decoder runtime (fun index : Nat => (index : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime ^ 2,
            type_of% (support_from_precision runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported samples budget)) ∧
  ∀ key : ZMod 2,
    ∀ supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => (actor.val : ZMod 2))).support,
      ∀ samples : Window runtime.tick.next (maximumIndex runtime.tick.next),
        ∀ budget : SourceWindowPrecision.gain runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0 *
          SourceWindowPrecision.sampleEnergy runtime.tick.next (maximumIndex runtime.tick.next)
            (samples - recordedPrefix runtime.tick.next (maximumIndex runtime.tick.next) 0 ((maximumIndex runtime.tick.next).val + 1)
              (decoder runtime.tick.next (fun index : Nat => (index : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime.tick.next ^ 2,
          type_of% (next_support runtime (fun index : Nat => (index : ZMod 2)) key supported samples budget)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes,
    fun nonunit => ⟨fun actor => actor_tail_zero runtime nonunit actor,
      fun key => ⟨decoder_tail_zero runtime nonunit (fun index : Nat => (index : ZMod 2)) key,
        model_source runtime nonunit (fun index : Nat => (index : ZMod 2)) key,
        fun supported => ⟨exact_support runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported,
          fun samples => ⟨model_realization runtime nonunit samples, bias_bound runtime nonunit (fun index : Nat => (index : ZMod 2)) key samples,
            fun budget => support_from_precision runtime nonunit (fun index : Nat => (index : ZMod 2)) key supported samples budget⟩⟩⟩⟩,
    fun key supported samples budget => next_support runtime (fun index : Nat => (index : ZMod 2)) key supported samples budget⟩

end
end SourceWindowPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
