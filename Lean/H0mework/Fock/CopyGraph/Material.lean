import H0mework.Fock.CopyGraph.Native

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyLiveModelFamily

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def CurrentLaw (runtime : LivingRuntimeState process) : Prop :=
  (∀ index : Index (inventoryBound runtime),
    type_of% (actor_birth runtime index) ∧ type_of% (family_source runtime index) ∧
      type_of% (family_read runtime index) ∧ type_of% (original_remaining runtime index) ∧
      type_of% (original_reconstruction runtime index) ∧ type_of% (family_energy runtime index) ∧
      ∀ ticks : Nat, type_of% (family_future_read runtime index ticks)) ∧
    type_of% (SourceCopyCurrentCoordinates.shared_family runtime) ∧
    type_of% (SourceCopyCurrentCoordinates.shared_next runtime) ∧
    type_of% (SourceCopyCurrentCoordinates.joint_model_step runtime) ∧
    type_of% (SourceCopyCurrentCoordinates.joint_dimension runtime) ∧
    type_of% (SourceCopyCurrentCoordinates.linear_code_lower runtime) ∧
    type_of% (SourceCopyCurrentCoordinates.shared_reconstruction runtime) ∧
    type_of% (SourceCopyCurrentCoordinates.shared_energy runtime) ∧
    ∀ index : Index (inventoryBound runtime), ∀ ticks : Nat,
      type_of% (SourceCopyCurrentCoordinates.shared_original_read runtime index ticks)

theorem current_law (runtime : LivingRuntimeState process) : CurrentLaw runtime := by
  dsimp only [CurrentLaw]
  with_reducible exact ⟨(fun index => ⟨actor_birth runtime index, family_source runtime index, family_read runtime index,
    original_remaining runtime index, original_reconstruction runtime index, family_energy runtime index,
    family_future_read runtime index⟩), SourceCopyCurrentCoordinates.shared_family runtime,
    SourceCopyCurrentCoordinates.shared_next runtime, SourceCopyCurrentCoordinates.joint_model_step runtime,
    SourceCopyCurrentCoordinates.joint_dimension runtime, SourceCopyCurrentCoordinates.linear_code_lower runtime,
    SourceCopyCurrentCoordinates.shared_reconstruction runtime, SourceCopyCurrentCoordinates.shared_energy runtime,
    SourceCopyCurrentCoordinates.shared_original_read runtime⟩

def MaterialLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  next runtime (family runtime) = family material.next ∧ CurrentLaw material.next ∧
    (∀ index : Index (inventoryBound material.next), ∀ fresh : ¬ index.val ≤ inventoryBound runtime,
      type_of% (newborn_material runtime index fresh)) ∧
    (∀ index : Index (inventoryBound runtime),
      type_of% (current_index_material runtime index 1) ∧ type_of% (budget_material_current runtime index)) ∧
    type_of% material.factorizes ∧ type_of% (coversAt_factorizes material.next .particleWave) ∧
    type_of% (SourceCopySharedNext.update_native runtime) ∧ type_of% (SourceCopySharedNext.updated_family runtime) ∧
    type_of% (SourceCopySharedNext.native_model_update runtime) ∧ type_of% (SourceCopySharedNext.native_budget runtime) ∧
    type_of% (SourceCopySharedNext.no_free_update runtime) ∧ type_of% (SourceCopySharedNext.packet_count runtime) ∧
    ∀ phase : Fin ((SourceCopyCurrentCoordinates.maximumIndex runtime.tick.next).val + 1),
      type_of% (SourceCopySharedNext.native_packet_source runtime phase) ∧
      type_of% (SourceCopySharedNext.native_forcing runtime phase) ∧ type_of% (SourceCopySharedNext.native_conditional runtime phase)

theorem material_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    MaterialLaw runtime material := by
  dsimp only [MaterialLaw]
  refine ⟨family_next runtime, current_law material.next, newborn_material runtime,
    (fun index => ⟨current_index_material runtime index 1, budget_material_current runtime index⟩),
    material.factorizes, coversAt_factorizes material.next .particleWave, ?_⟩
  with_reducible exact ⟨SourceCopySharedNext.update_native runtime, SourceCopySharedNext.updated_family runtime,
    SourceCopySharedNext.native_model_update runtime, SourceCopySharedNext.native_budget runtime,
    SourceCopySharedNext.no_free_update runtime, SourceCopySharedNext.packet_count runtime,
    fun phase => ⟨SourceCopySharedNext.native_packet_source runtime phase,
      SourceCopySharedNext.native_forcing runtime phase, SourceCopySharedNext.native_conditional runtime phase⟩⟩

end
end SourceCopyLiveModelFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
