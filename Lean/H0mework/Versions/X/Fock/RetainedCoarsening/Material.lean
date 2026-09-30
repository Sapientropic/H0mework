import H0mework.Versions.X.Fock.RetainedCoarsening.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open SourceConditionalModel (Actors)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ (nonunit : (maximumIndex runtime).val ≠ 0)
      (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
        SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
      (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
        SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
          (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
            SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
              (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) < SourcePosteriorStability.threshold runtime ^ 2) (steps : Nat),
    let initial := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    let current := SourceRetainedReceiver.trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
    type_of% (merge_trajectory runtime initial (clockRead 0) forgetClock (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) rfl steps) ∧ type_of% (merge_next (runtime.advance steps) current (clockRead 0) forgetClock (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps)) ∧
    (∀ key : ZMod 2, type_of% (residual_merge (runtime.advance steps) current forgetClock key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound (runtime.advance steps))).map (fun actor : Actors (runtime.advance steps) => forgetClock (clockRead 0 actor.val))).support, type_of% (conditional_error (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) current (clockRead 0) forgetClock key (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) supported)) ∧
    (∀ depth : Nat, type_of% (field_balance (runtime.advance steps) current depth (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps)) ∧ type_of% (field_information (runtime.advance steps) current depth))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  refine ⟨material.factorizes, ?_⟩
  intro nonunit samples budgets steps
  let initial : SourceRetainedReceiver.At runtime (ℤ × ℤ) := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
  let current := SourceRetainedReceiver.trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
  with_reducible exact ⟨merge_trajectory runtime initial (clockRead 0) forgetClock (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) rfl steps, merge_next (runtime.advance steps) current (clockRead 0) forgetClock (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps),
    fun key => ⟨residual_merge (runtime.advance steps) current forgetClock key, fun supported => conditional_error (runtime.advance steps) (SourceRetainedReceiver.trajectory_nonunit runtime nonunit steps) current (clockRead 0) forgetClock key (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps) supported⟩,
    fun depth => ⟨field_balance (runtime.advance steps) current depth (SourceRetainedReceiver.trajectory_native runtime initial (clockRead 0) (SourceRetainedReceiver.start_native runtime nonunit (clockRead 0) samples budgets) steps) (SourceRetainedReceiver.trajectory_keys runtime initial (clockRead 0) rfl steps), field_information (runtime.advance steps) current depth⟩⟩

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
