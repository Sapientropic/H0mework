import H0mework.Versions.X.Fock.CopyGraph.ConditionalField
import H0mework.Versions.X.Fock.CopyGraph.ConditionalEffect
import H0mework.Versions.X.Fock.HistoryCopy.InformationTrace

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedAcquisitionContinuation
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

local instance observationParentMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    (∀ value : FieldSpace depth depth,
      type_of% (original_compression_error depth depth index (SourceCopyObservation.before depth depth) value) ∧
      type_of% (original_compression_error depth depth index (SourceCopyObservation.joint depth depth index) value) ∧
      type_of% (original_residual_mass depth depth (SourceCopyObservation.joint depth depth index) value) ∧
      type_of% (original_residual_bound depth depth index (SourceCopyObservation.joint depth depth index) value) ∧
      ∀ actor : Fin (depth + 1), type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
        (residual (historyPMF depth) (SourceCopyObservation.joint depth depth index)
          (Actor.currentPullback depth depth value)) actor)) ∧
    (∀ atom : ParentCarrier × ParentCarrier,
      ∀ supported : atom ∈ (observed (historyPMF depth) (SourceCopyObservation.joint depth depth index)).support,
        type_of% (original_clock_conditional depth depth (SourceCopyObservation.joint depth depth index) atom supported)) ∧
    (∀ actor : Fin (depth + 1), type_of% (SourceGeneratedJointClock.signal_model depth actor)) ∧
    type_of% (SourceCopyInventory.normal_copy_cost runtime index) ∧
    type_of% (SourceCopyInventory.generated_next_copy_cost runtime index) ∧
    type_of% (coversAt_factorizes runtime .particleWave) ∧
    type_of% (coversAt_factorizes runtime.tick.next .particleWave)

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  exact ⟨(fun value => ⟨original_compression_error _ _ index _ value, original_compression_error _ _ index _ value,
    original_residual_mass _ _ _ value, original_residual_bound _ _ index _ value,
    SourceGeneratedConditionalInventory.full_record_read runtime _ _⟩),
    original_clock_conditional _ _ _, SourceGeneratedJointClock.signal_model _,
    SourceCopyInventory.normal_copy_cost runtime index, SourceCopyInventory.generated_next_copy_cost runtime index,
    coversAt_factorizes runtime .particleWave, coversAt_factorizes runtime.tick.next .particleWave⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    type_of% (SourceCopyProgram.copy_current round) ∧
      ∀ index : Index depth, ObservationAt (roundRuntime round) index ∧
        ∀ value : FieldSpace depth depth,
          SourceCopyGraph.FieldAt round depth depth index (Actor.currentTransfer depth depth
            (residual (historyPMF depth) (SourceCopyObservation.before depth depth) (Actor.currentPullback depth depth value))) ∧
          SourceCopyGraph.FieldAt round depth depth index (Actor.currentTransfer depth depth
            (residual (historyPMF depth) (SourceCopyObservation.joint depth depth index) (Actor.currentPullback depth depth value)))

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  exact ⟨SourceCopyProgram.copy_current round,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun _ => ⟨SourceCopyGraph.original_field_consumed round _ _ index _,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceConditionalGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
