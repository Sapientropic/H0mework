import H0mework.Versions.X.Fock.HistoryConditional.ModelAccount
import H0mework.Versions.X.Fock.HistoryConditional.Installed
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesShared

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModel

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedActionObservationHistory (projection)
open SourceCopyCurrentCoordinates (jointObserver jointModelEquiv shared)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem original_runtime (runtime : LivingRuntimeState process) : runtimeAt (inventoryBound runtime) = runtime := by
  rw [inventory_bound]
  exact (runtime_eq runtime).symm

theorem last_model (runtime : LivingRuntimeState process) :
    nextRead runtime (Fin.last (inventoryBound runtime)) = (jointModelEquiv runtime.tick.next).symm (shared runtime.tick.next) := by
  have actual := congrArg (fun current : LivingRuntimeState process => current.tick.next) (original_runtime runtime)
  change projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
    (sourceValue (runtimeAt (inventoryBound runtime)).tick.next) = _
  rw [actual, SourceCopyCurrentCoordinates.shared_source]
  exact ((jointModelEquiv runtime.tick.next).symm_apply_eq.mpr
    (SourceCopyCurrentCoordinates.joint_model_source runtime.tick.next (sourceValue runtime.tick.next)).symm).symm

theorem current_model_recovered (runtime : LivingRuntimeState process) :
    modelEstimate runtime (fullRead runtime (Fin.last (inventoryBound runtime))) (full_supported runtime (Fin.last (inventoryBound runtime))) =
      (jointModelEquiv runtime.tick.next).symm (shared runtime.tick.next) :=
  (model_recovers runtime (Fin.last (inventoryBound runtime))).trans (last_model runtime)

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% (original_runtime runtime) ∧ type_of% (current_model_recovered runtime) ∧
    (∀ index : Actors runtime, type_of% (next_action runtime index) ∧ type_of% (clock_original runtime index) ∧
      type_of% (full_conditional_model runtime index) ∧ type_of% (model_recovers runtime index) ∧ type_of% (full_same_material runtime index)) ∧
    (∀ depth : Nat, ∀ decode : NextModel runtime → ℂ, type_of% (variance_original_account runtime depth decode) ∧
      ∀ decoder : Field parity → ℂ, type_of% (original_conditional_error runtime depth decode decoder) ∧
        type_of% (original_complete_account runtime depth decode decoder)) ∧
    (∀ enough : 2 ≤ inventoryBound runtime, ∀ depth : Nat,
      type_of% (dynamic_information_positive runtime enough depth) ∧ type_of% (no_dynamic_decoder runtime enough depth) ∧
      ∀ decoder : Field parity → ℂ, type_of% (original_error_lower runtime enough depth decoder)) ∧
    type_of% (conditional_original runtime) ∧ type_of% (mean_original runtime) ∧ type_of% (full_information_zero runtime) ∧
    (∀ decode : NextModel runtime → ℂ, type_of% (original_task_cost_zero runtime decode) ∧ type_of% (original_residual_zero runtime decode)) ∧
    type_of% (SourceConditionalHistory.Fock.runtime_conditional_factorizes (inventoryBound runtime)) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨original_runtime runtime, current_model_recovered runtime,
    (fun index => ⟨next_action runtime index, clock_original runtime index, full_conditional_model runtime index,
      model_recovers runtime index, full_same_material runtime index⟩),
    (fun depth decode => ⟨variance_original_account runtime depth decode, fun decoder =>
      ⟨original_conditional_error runtime depth decode decoder, original_complete_account runtime depth decode decoder⟩⟩),
    (fun enough depth => ⟨dynamic_information_positive runtime enough depth, no_dynamic_decoder runtime enough depth,
      original_error_lower runtime enough depth⟩),
    conditional_original runtime, mean_original runtime, full_information_zero runtime,
    (fun decode => ⟨original_task_cost_zero runtime decode, original_residual_zero runtime decode⟩),
    SourceConditionalHistory.Fock.runtime_conditional_factorizes (inventoryBound runtime), material.factorizes⟩

end
end SourceConditionalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
