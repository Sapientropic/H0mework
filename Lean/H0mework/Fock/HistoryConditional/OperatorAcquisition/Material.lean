import H0mework.Fock.HistoryConditional.OperatorAcquisition.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationAcquisition

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ index : Index (inventoryBound runtime), ∀ nonunit : index.val ≠ 0, ∀ steps : Nat,
    type_of% (SourceGraphRecurrence.material_history_step runtime index (steps + 1)) ∧
    type_of% (source_law runtime index nonunit steps) ∧
    type_of% (shorter_inventory runtime index steps) ∧
    (∀ value : SourceJointClockGraph.Carrier,
      type_of% (decode_source runtime index nonunit steps value) ∧
      type_of% (acquire_source runtime index nonunit steps value) ∧
      type_of% (residual_budget runtime index nonunit steps value)) ∧
    type_of% (acquired_strict runtime index nonunit steps) ∧
    type_of% (native_next runtime index nonunit steps) ∧
    type_of% (native_acquired_next runtime index nonunit steps) ∧
    (∀ phase : Fin (index.val + 1), type_of% (SourceCopyFutureUpdate.native_query runtime index steps 0 phase)) ∧
    ∀ key : ZMod 2,
      type_of% (model_feedback runtime index nonunit steps (fun index : Nat => (index : ZMod 2)) key) ∧
      ∀ supported : key ∈ ((historyPMF (inventoryBound runtime)).map
        (fun actor : SourceConditionalModel.Actors runtime => (actor.val : ZMod 2))).support,
      ∀ depth : Nat, type_of% (field_cost runtime index nonunit steps depth key supported)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun index nonunit steps =>
    ⟨SourceGraphRecurrence.material_history_step runtime index (steps + 1), source_law runtime index nonunit steps,
      shorter_inventory runtime index steps, fun value => ⟨decode_source runtime index nonunit steps value,
        acquire_source runtime index nonunit steps value, residual_budget runtime index nonunit steps value⟩,
      acquired_strict runtime index nonunit steps, native_next runtime index nonunit steps,
      native_acquired_next runtime index nonunit steps, fun phase => SourceCopyFutureUpdate.native_query runtime index steps 0 phase,
      fun key => ⟨model_feedback runtime index nonunit steps (fun index : Nat => (index : ZMod 2)) key,
        fun supported depth => field_cost runtime index nonunit steps depth key supported⟩⟩⟩

end
end SourceOperatorObservationAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
