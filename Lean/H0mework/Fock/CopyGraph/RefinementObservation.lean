import H0mework.Fock.CopyGraph.RefinementNative
import H0mework.Fock.CopyGraph.RefinementJoint

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyObservation (before joint twoMaterial)
open SourceCopyProgram (Index sourceDepth)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance observationParentMeasurable : MeasurableSpace ParentCarrier := ⊤

def ObservationAt (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : Prop :=
    let depth := inventoryBound runtime
    PrefixAt runtime index ∧
      (∀ value : SourceJointClockGraph.Carrier,
        type_of% (joint_residual_update depth depth index value) ∧ type_of% (joint_cost_gain depth depth index value) ∧
        type_of% (no_gain_iff depth depth index (joint depth depth index) Prod.fst value)) ∧
      (∀ value : FieldSpace depth depth,
        let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
        let gained := SourceConditionalGraphDecoder.fieldDecode depth depth index (joint depth depth index) target -
          SourceConditionalGraphDecoder.fieldDecode depth depth index (before depth depth) target
        type_of% (original_error_gain depth depth index (joint depth depth index) Prod.fst value) ∧
        type_of% (conditional_budget depth depth index (joint depth depth index) Prod.fst (Actor.currentPullback depth depth value)) ∧
        ∀ actor : Fin (depth + 1), type_of% (SourceGeneratedConditionalInventory.full_record_read runtime depth
          (Actor.currentPullback depth depth gained) actor)) ∧
      SourceConditionalCost.ObservationAt runtime index

theorem observation_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ObservationAt runtime index := by
  dsimp only [ObservationAt]
  with_reducible exact ⟨prefix_consumed runtime index,
    (fun value => ⟨joint_residual_update _ _ index value, joint_cost_gain _ _ index value, no_gain_iff _ _ index _ _ value⟩),
    (fun value => ⟨original_error_gain _ _ index _ _ value,
      conditional_budget _ _ index _ _ (Actor.currentPullback _ _ value), SourceGeneratedConditionalInventory.full_record_read runtime _ _⟩),
    SourceConditionalCost.observation_consumed runtime index⟩

def ActualRecovery : Prop :=
    (∀ value : FieldSpace 3 3, type_of% (actual_joint_residual_zero (Actor.currentPullback 3 3 value)) ∧
      type_of% (actual_joint_gain (Actor.currentPullback 3 3 value))) ∧
      type_of% actual_clock_gain_positive ∧ SourceConditionalCost.ActualRecovery

theorem actual_recovery_consumed : ActualRecovery := by
  dsimp only [ActualRecovery]
  with_reducible exact ⟨(fun value => ⟨actual_joint_residual_zero (Actor.currentPullback 3 3 value),
    actual_joint_gain (Actor.currentPullback 3 3 value)⟩), actual_clock_gain_positive, SourceConditionalCost.actual_recovery_consumed⟩

def RoundAt (round : Nat) : Prop :=
    let depth := sourceDepth round
    SourceConditionalCost.RoundAt round ∧ ActualRecovery ∧
      ∀ index : Index depth, ObservationAt (roundRuntime round) index ∧
        ∀ value : FieldSpace depth depth,
          let target := SourceCopyGraph.action depth index (fieldRead depth depth value)
          let fine := SourceConditionalGraphDecoder.fieldDecode depth depth index (joint depth depth index) target
          let coarse := SourceConditionalGraphDecoder.fieldDecode depth depth index (before depth depth) target
          type_of% (gain_realization round depth depth index (joint depth depth index) Prod.fst target) ∧
          SourceCopyGraph.FieldAt round depth depth index (fine - coarse) ∧
          SourceCopyGraph.FieldAt round depth depth index (value - fine) ∧
          SourceCopyGraph.FieldAt round depth depth index (value - coarse)

theorem round_consumed (round : Nat) : RoundAt round := by
  dsimp only [RoundAt]
  exact ⟨SourceConditionalCost.round_consumed round, actual_recovery_consumed,
    fun index => ⟨observation_consumed (roundRuntime round) index,
      fun _ => ⟨gain_realization round _ _ index _ _ _,
        SourceCopyGraph.original_field_consumed round _ _ index _,
        SourceCopyGraph.original_field_consumed round _ _ index _,
        SourceCopyGraph.original_field_consumed round _ _ index _⟩⟩⟩

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
