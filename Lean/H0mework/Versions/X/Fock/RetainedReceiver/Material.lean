import H0mework.Versions.X.Fock.RetainedReceiver.Feedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
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
    let initial := start (inventoryBound runtime) (maximumIndex runtime).val nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
    let current := trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
    type_of% (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) ∧
    type_of% (trajectory_keys runtime initial (clockRead 0) rfl steps) ∧
    (∀ key : ℤ × ℤ,
      type_of% (reconstruction (runtime.advance steps) (trajectory_nonunit runtime nonunit steps) current key) ∧
      type_of% (continued_model runtime nonunit (clockRead 0) samples key budgets steps) ∧
      type_of% (continued_bound runtime nonunit (clockRead 0) samples key budgets steps) ∧
      type_of% (trajectory_residual runtime initial (clockRead 0) key (start_native runtime nonunit (clockRead 0) samples budgets) steps) ∧
      type_of% (trajectory_energy runtime initial (clockRead 0) key (start_native runtime nonunit (clockRead 0) samples budgets) steps) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound (runtime.advance steps))).map (fun actor : Actors (runtime.advance steps) => clockRead 0 actor.val)).support, type_of% (conditional_error (runtime.advance steps) (trajectory_nonunit runtime nonunit steps) current (clockRead 0) key (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) supported)) ∧
    (∀ actor : Actors (runtime.advance steps),
      type_of% (clock_recovers (runtime.advance steps) current (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) actor) ∧
      type_of% (history_next (runtime.advance steps) current (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) actor)) ∧
    (∀ depth : Nat,
      type_of% (field_information (runtime.advance steps) current depth) ∧
      type_of% (field_source (runtime.advance steps) current depth (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) (trajectory_keys runtime initial (clockRead 0) rfl steps)) ∧
      type_of% (field_loss (runtime.advance steps) current (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) (trajectory_keys runtime initial (clockRead 0) rfl steps) depth))

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  refine ⟨material.factorizes, ?_⟩
  intro nonunit samples budgets steps
  let initial : At runtime (ℤ × ℤ) := start (inventoryBound runtime) (maximumIndex runtime).val nonunit (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)) samples
  let current := trajectory runtime initial (fun offset => clockRead 0 (inventoryBound runtime + offset + 1)) steps
  with_reducible exact ⟨trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps,
    trajectory_keys runtime initial (clockRead 0) rfl steps,
    fun key => ⟨reconstruction (runtime.advance steps) (trajectory_nonunit runtime nonunit steps) current key,
      continued_model runtime nonunit (clockRead 0) samples key budgets steps,
      continued_bound runtime nonunit (clockRead 0) samples key budgets steps,
      trajectory_residual runtime initial (clockRead 0) key (start_native runtime nonunit (clockRead 0) samples budgets) steps,
      trajectory_energy runtime initial (clockRead 0) key (start_native runtime nonunit (clockRead 0) samples budgets) steps,
      fun supported => conditional_error (runtime.advance steps) (trajectory_nonunit runtime nonunit steps) current (clockRead 0) key (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) supported⟩,
    fun actor => ⟨clock_recovers (runtime.advance steps) current (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) actor,
      history_next (runtime.advance steps) current (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) actor⟩,
    fun depth => ⟨field_information (runtime.advance steps) current depth,
      field_source (runtime.advance steps) current depth (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) (trajectory_keys runtime initial (clockRead 0) rfl steps),
      field_loss (runtime.advance steps) current (trajectory_native runtime initial (clockRead 0) (start_native runtime nonunit (clockRead 0) samples budgets) steps) (trajectory_keys runtime initial (clockRead 0) rfl steps) depth⟩⟩

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
