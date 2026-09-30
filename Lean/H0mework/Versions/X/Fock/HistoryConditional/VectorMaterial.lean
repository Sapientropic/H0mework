import H0mework.Versions.X.Fock.HistoryConditional.VectorAccount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors nextRead dynamicRead fullRead full_supported positive)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open SourceWeightedRecovery (observed_supported)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem current_source_recovered (runtime : LivingRuntimeState process) :
    realizeModel runtime (estimate runtime (fullRead runtime) (fullRead runtime (Fin.last (inventoryBound runtime)))
      (full_supported runtime (Fin.last (inventoryBound runtime)))) = SourceCopyNativeModelStep.sourceValue runtime.tick.next := by
  rw [full_recovers]
  change SourceCopyNativeModelStep.sourceValue (runtimeAt (inventoryBound runtime)).tick.next = _
  rw [SourceConditionalModel.original_runtime]

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% (current_source_recovered runtime) ∧
  (∀ index : Actors runtime, type_of% (actor_material runtime index) ∧ type_of% (realized_next runtime index) ∧
    type_of% (full_recovers runtime index) ∧ type_of% (full_remaining_zero runtime index)) ∧
  (∀ depth : Nat,
    (∀ index : Actors runtime,
      type_of% (mean_action runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
        (observed_supported _ _ index (positive runtime index))) ∧
      type_of% (variance_action runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
        (observed_supported _ _ index (positive runtime index))) ∧
      type_of% (mean_energy runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
        (observed_supported _ _ index (positive runtime index))) ∧
      ∀ actor : Actors runtime,
        type_of% (remaining_action runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
          (observed_supported _ _ index (positive runtime index)) actor) ∧
        type_of% (reconstruction runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
          (observed_supported _ _ index (positive runtime index)) actor)) ∧
    (∀ decoder : Field parity → SourceJointClockGraph.Carrier,
      type_of% (dynamic_error_decomposition runtime depth decoder) ∧ type_of% (dynamic_optimal runtime depth decoder)) ∧
    type_of% (dynamic_attains runtime depth) ∧
    (∀ enough : 2 ≤ inventoryBound runtime, type_of% (dynamic_variance_lower runtime enough depth) ∧
      ∀ decoder : Field parity → SourceJointClockGraph.Carrier, type_of% (dynamic_error_lower runtime enough depth decoder)) ∧
    ∀ decode : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ,
      type_of% (scalar_account runtime depth decode) ∧ ∀ index : Actors runtime, type_of% (scalar_transfer runtime depth decode index)) ∧
  type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨current_source_recovered runtime,
    (fun index => ⟨actor_material runtime index, realized_next runtime index, full_recovers runtime index, full_remaining_zero runtime index⟩),
    (fun depth => ⟨(fun index => ⟨mean_action runtime (dynamicRead runtime depth) (dynamicRead runtime depth index) _,
      variance_action runtime (dynamicRead runtime depth) (dynamicRead runtime depth index) _,
      mean_energy runtime (dynamicRead runtime depth) (dynamicRead runtime depth index) _,
      fun actor => ⟨remaining_action runtime (dynamicRead runtime depth) (dynamicRead runtime depth index) _ actor,
        reconstruction runtime (dynamicRead runtime depth) (dynamicRead runtime depth index) _ actor⟩⟩),
      (fun decoder => ⟨dynamic_error_decomposition runtime depth decoder, dynamic_optimal runtime depth decoder⟩),
      dynamic_attains runtime depth, fun enough => ⟨dynamic_variance_lower runtime enough depth, dynamic_error_lower runtime enough depth⟩,
      fun decode => ⟨scalar_account runtime depth decode, scalar_transfer runtime depth decode⟩⟩), material.factorizes⟩

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
