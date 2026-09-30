import H0mework.Versions.X.Fock.CopyComplete.Observation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourcePrimeHistoryRecovery
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2
local instance windowMeasurable (width : Nat) : MeasurableSpace (SourceFixedInventoryRecovery.Observation width) := ⊤

abbrev query (runtime : LivingRuntimeState process) :=
  SourceFixedInventoryRecovery.query runtime (windowBound sourceOwner (inventoryBound runtime))

theorem model_represented (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    value ∈ Set.range (SourceConditionalGraphDecoder.realizeObserved (inventoryBound runtime) (inventoryBound runtime)
      (Hilbert.read model (inventoryBound runtime))) := by
  refine ⟨SourceConditionalGraphDecoder.decode (inventoryBound runtime) (inventoryBound runtime) index
    (Hilbert.read model (inventoryBound runtime))
    (SourceCopyGraph.action (inventoryBound runtime) index (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)), ?_⟩
  exact SourceCompleteGraph.field_recovery model _ _ index value

theorem window_represented (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    value ∈ Set.range (SourceConditionalGraphDecoder.realizeObserved (inventoryBound runtime) (inventoryBound runtime) (query runtime)) := by
  refine ⟨SourceConditionalGraphDecoder.decode (inventoryBound runtime) (inventoryBound runtime) index (query runtime)
    (SourceCopyGraph.action (inventoryBound runtime) index (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)), ?_⟩
  exact SourceGraphRefinement.complete_field_recovery runtime index value

theorem model_minimum (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    IsMinOn (fun value : FieldSpace (inventoryBound runtime) (inventoryBound runtime) =>
      ‖target - SourceCopyGraph.action (inventoryBound runtime) index (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)‖ ^ 2)
      Set.univ (SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
        (Hilbert.read model (inventoryBound runtime)) target) := by
  intro value _
  exact (SourceConditionalGraphDecoder.original_minimum _ _ index _ target).2
    (model_represented model runtime index value)

theorem window_minimum (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    IsMinOn (fun value : FieldSpace (inventoryBound runtime) (inventoryBound runtime) =>
      ‖target - SourceCopyGraph.action (inventoryBound runtime) index (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)‖ ^ 2)
      Set.univ (SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (query runtime) target) := by
  intro value _
  exact (SourceConditionalGraphDecoder.original_minimum _ _ index _ target).2 (window_represented runtime index value)

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
