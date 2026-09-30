import H0mework.Fock.CopyFiniteComplete.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2 windowMeasurable

private theorem cost_equal (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime
    let finiteValue := SourceConditionalGraphDecoder.fieldDecode depth depth index (query runtime) target
    let modelValue := SourceConditionalGraphDecoder.fieldDecode depth depth index (Hilbert.read model depth) target
    ‖target - SourceCopyGraph.action depth index (fieldRead depth depth finiteValue)‖ ^ 2 =
      ‖target - SourceCopyGraph.action depth index (fieldRead depth depth modelValue)‖ ^ 2 := by
  dsimp only
  have toFinite := (model_minimum model runtime index target) (Set.mem_univ
    (SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (query runtime) target))
  have toModel := (window_minimum runtime index target) (Set.mem_univ
    (SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) target))
  exact le_antisymm toModel toFinite

private theorem model_cost (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime
    let full := Hilbert.read model depth
    ‖target - SourceCopyGraph.action depth index (fieldRead depth depth
      (SourceConditionalGraphDecoder.fieldDecode depth depth index full target))‖ ^ 2 =
        ‖SourceConditionalGraphDecoder.residual depth depth index full target‖ ^ 2 := by
  dsimp only
  change ‖target - SourceCopyGraph.action (inventoryBound runtime) index
    (fieldRead (inventoryBound runtime) (inventoryBound runtime)
      (SourceConditionalGraphDecoder.realizeObserved (inventoryBound runtime) (inventoryBound runtime)
        (Hilbert.read model (inventoryBound runtime))
        (SourceConditionalGraphDecoder.decode (inventoryBound runtime) (inventoryBound runtime) index
          (Hilbert.read model (inventoryBound runtime)) target)))‖ ^ 2 = _
  rw [SourceConditionalGraphDecoder.realized_action]
  exact SourceConditionalGraphDecoder.minimum_cost _ _ index _ target

private theorem model_unique (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) (candidate : FieldSpace (inventoryBound runtime) (inventoryBound runtime))
    (attained : ‖target - SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime) (inventoryBound runtime) candidate)‖ ^ 2 =
        ‖SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index
          (Hilbert.read model (inventoryBound runtime)) target‖ ^ 2) :
    candidate = SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) target := by
  let depth := inventoryBound runtime
  let full := Hilbert.read model depth
  obtain ⟨proposal, represented⟩ := model_represented model runtime index candidate
  have observedCost : ‖target - SourceConditionalGraphDecoder.action depth depth index full proposal‖ ^ 2 =
      ‖SourceConditionalGraphDecoder.residual depth depth index full target‖ ^ 2 := by
    rw [← SourceConditionalGraphDecoder.realized_action, represented]
    with_reducible exact attained
  have same := (SourceConditionalGraphDecoder.minimum_fibre depth depth index full target proposal).mp observedCost
  rw [← represented, same]
  rfl

theorem decoder_value (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) target =
      SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (query runtime) target := by
  apply Eq.symm
  apply model_unique model runtime index target
  exact (cost_equal model runtime index target).trans (model_cost model runtime index target)

theorem decoder_linear (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) =
      SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (query runtime) := by
  apply ContinuousLinearMap.ext
  exact decoder_value model runtime index

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
