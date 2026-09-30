import H0mework.Versions.X.Fock.HistoryConditional.VectorRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors NextModel nextRead dynamicRead positive)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceWeightedRecovery (observed_supported taskValue)
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem scalar_transfer (runtime : LivingRuntimeState process) (depth : Nat)
    (decode : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ) (index : Actors runtime) :
    decode (realizeModel runtime (dynamicEstimate runtime depth index)) =
      SourceWeightedRecovery.transfer (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
        (taskValue (historyPMF (inventoryBound runtime)) (decode ∘ realizeModel runtime ∘ nextRead runtime))
          (dynamicRead runtime depth index) :=
  (scalar_mean runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
    (observed_supported _ _ index (positive runtime index)) decode).trans
      (SourceWeightedRecovery.optimal_is_conditional _ _ _ _ _).symm

theorem scalar_variance (runtime : LivingRuntimeState process) (depth : Nat)
    (decode : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ) (index : Actors runtime) :
    SourceConditionalNext.variance (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
      (SourceConditionalNext.Image.actual (nextRead runtime)) (fun item => decode (realizeModel runtime item.val))
      (dynamicRead runtime depth index) (observed_supported _ _ index (positive runtime index)) =
    ∑ j : Actors runtime,
      (posterior runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
        (observed_supported _ _ index (positive runtime index)) j).toReal *
      ‖decode (remaining runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
        (observed_supported _ _ index (positive runtime index)) j)‖ ^ 2 := by
  rw [SourceConditionalNext.variance_is_conditional]
  have generated := SourceConditionalNext.Image.mean_original (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
    (nextRead runtime) (fun model => decode (realizeModel runtime model))
    (dynamicRead runtime depth index) (observed_supported _ _ index (positive runtime index))
  have original := scalar_mean runtime (dynamicRead runtime depth) (dynamicRead runtime depth index)
    (observed_supported _ _ index (positive runtime index)) decode
  simp only [Function.comp_def] at generated original
  rw [generated, ← original]
  simp only [SourceConditionalNext.Image.actual_value, remaining, map_sub, realized_next]

theorem scalar_account (runtime : LivingRuntimeState process) (depth : Nat)
    (decode : SourceJointClockGraph.Carrier →ₗ[ℂ] ℂ) :
    let value := taskValue (historyPMF (inventoryBound runtime)) (decode ∘ realizeModel runtime ∘ nextRead runtime)
    let retained := SourceGeneratedEmpiricalHilbert.retainedHistory parity runtimeSeed (inventoryBound runtime) (depth + 1)
      (SourceWeightedRecovery.Runtime.Actor.actorTransfer parity runtimeSeed (inventoryBound runtime) value)
    (∑ i : Actors runtime, (historyPMF (inventoryBound runtime) i).toReal *
      ∑ j : Actors runtime, (posterior runtime (dynamicRead runtime depth) (dynamicRead runtime depth i)
        (observed_supported _ _ i (positive runtime i)) j).toReal *
        ‖decode (remaining runtime (dynamicRead runtime depth) (dynamicRead runtime depth i)
          (observed_supported _ _ i (positive runtime i)) j)‖ ^ 2) =
      ‖SourceWeightedRecovery.Runtime.Actor.actorResidual parity runtimeSeed (inventoryBound runtime) value‖ ^ 2 +
        SourceGeneratedEmpiricalHilbert.inventoryEnergy parity runtimeSeed (inventoryBound runtime) (depth + 1) retained.2 := by
  have paid := SourceConditionalModel.variance_original_account runtime depth (decode ∘ realizeModel runtime)
  simpa only [Function.comp_apply, Function.comp_assoc, scalar_variance] using paid

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
