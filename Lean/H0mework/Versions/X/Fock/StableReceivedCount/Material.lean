import H0mework.Versions.X.Fock.StableReceivedCount.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceStableReceivedCount

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ (nonunit : (maximumIndex runtime).val ≠ 0)
      (samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)),
    type_of% (support_source runtime nonunit samples) ∧
    (∀ selected : Bool, type_of% (model_realization runtime nonunit samples selected)) ∧
    ∀ (key : ZMod 2)
        (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
          SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
            (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
              SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
                (SourceConditionalNativePosterior.decoder runtime (fun n : Nat => (n : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime ^ 2),
      type_of% (count_complete runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
      type_of% (residual_from_precision runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
      type_of% (residual_energy runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
      type_of% (model_writeback runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime.tick.next)).map (fun actor : Actors runtime.tick.next => (actor.val : ZMod 2))).support,
        type_of% (model_error runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key supported budget)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun nonunit samples =>
    ⟨support_source runtime nonunit samples, fun selected => model_realization runtime nonunit samples selected,
      fun key budget => ⟨count_complete runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        residual_from_precision runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        residual_energy runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        model_writeback runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        fun supported => model_error runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key supported budget⟩⟩⟩

end
end SourceStableReceivedCount
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
