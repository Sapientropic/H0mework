import H0mework.Versions.X.Fock.FibreExactState.Feedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFibreExactState

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ nonunit : (maximumIndex runtime).val ≠ 0,
    (∀ samples : SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1),
      type_of% (reconstruction runtime nonunit samples) ∧
      ∀ (key : ZMod 2) (budget : SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
          SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
            (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 samples -
              SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
                (SourceConditionalNativePosterior.decoder runtime (fun n : Nat => (n : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime ^ 2),
        type_of% (restored_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
        type_of% (model_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
        type_of% (residual_bound runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget) ∧
        ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => (actor.val : ZMod 2))).support,
          type_of% (observed_error runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key supported budget)) ∧
    ∀ (received : ZMod 2 → SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
        (budgets : ∀ key : ZMod 2, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
          SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
            (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (received key) -
              SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
                (SourceConditionalNativePosterior.decoder runtime (fun n : Nat => (n : ZMod 2)) key)) < SourcePosteriorStability.threshold runtime ^ 2),
      type_of% (state_source runtime nonunit received (fun n : Nat => (n : ZMod 2)) budgets) ∧
      type_of% (next_source runtime nonunit received (fun n : Nat => (n : ZMod 2)) budgets) ∧
      ∀ key : ZMod 2,
        type_of% (next_model_source runtime nonunit received (fun n : Nat => (n : ZMod 2)) key budgets) ∧
        type_of% (next_residual runtime nonunit received (fun n : Nat => (n : ZMod 2)) key budgets)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun nonunit =>
    ⟨fun samples => ⟨reconstruction runtime nonunit samples, fun key budget =>
      ⟨restored_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        model_source runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        residual_bound runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key budget,
        fun supported => observed_error runtime nonunit samples (fun n : Nat => (n : ZMod 2)) key supported budget⟩⟩,
      fun received budgets => ⟨state_source runtime nonunit received (fun n : Nat => (n : ZMod 2)) budgets,
        next_source runtime nonunit received (fun n : Nat => (n : ZMod 2)) budgets,
        fun key => ⟨next_model_source runtime nonunit received (fun n : Nat => (n : ZMod 2)) key budgets,
          next_residual runtime nonunit received (fun n : Nat => (n : ZMod 2)) key budgets⟩⟩⟩⟩

end
end SourceFibreExactState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
