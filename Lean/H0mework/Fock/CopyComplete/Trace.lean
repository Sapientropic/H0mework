import H0mework.Fock.CopyComplete.Native

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedAcquisitionJoint SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

theorem field_realization (round model depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    let recovered := SourceConditionalGraphDecoder.fieldDecode depth bound index (Hilbert.read model bound)
      (SourceCopyGraph.action depth index (fieldRead depth bound value))
    let copied := SourceCopyGraph.complexAction depth index (word depth bound recovered)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        SourceCopyGraph.action depth index (fieldRead depth bound value) := by
  dsimp only
  refine (SourceCopyGraph.original_copy_realization round _ _ _ _).trans ?_
  rw [field_recovery]

theorem normal_consumed (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    type_of% ((SourceGeneratedAcquisitionContinuation.normal runtime).target_factorizes) ∧
      type_of% (SourceGraphRecurrence.normal_depth runtime) ∧ type_of% (SourceGraphRecurrence.next_depth runtime) ∧
      (∀ value : SourceJointClockGraph.Carrier,
        type_of% (history_energy model runtime index ((frontier runtime).stageCount + 1) value) ∧
        type_of% (history_energy model runtime index ((frontier runtime).stageCount + 2) value)) ∧
      (∀ value : FieldSpace (inventoryBound runtime + ((frontier runtime).stageCount + 1))
          (inventoryBound runtime + ((frontier runtime).stageCount + 1)),
        type_of% (history_field_recovery model runtime index ((frontier runtime).stageCount + 1) value)) ∧
      (∀ value : FieldSpace (inventoryBound runtime + ((frontier runtime).stageCount + 2))
          (inventoryBound runtime + ((frontier runtime).stageCount + 2)),
        type_of% (history_field_recovery model runtime index ((frontier runtime).stageCount + 2) value)) ∧
      type_of% (history_boundary_nonzero model runtime index ((frontier runtime).stageCount + 2)) ∧
      type_of% (coversAt_factorizes (SourceGeneratedAcquisitionContinuation.normal runtime).targetRuntime.tick.next .particleWave) := by
  with_reducible exact ⟨(SourceGeneratedAcquisitionContinuation.normal runtime).target_factorizes,
    SourceGraphRecurrence.normal_depth runtime, SourceGraphRecurrence.next_depth runtime,
    fun value => ⟨history_energy model runtime index _ value, history_energy model runtime index _ value⟩,
    history_field_recovery model runtime index _, history_field_recovery model runtime index _,
    history_boundary_nonzero model runtime index _, coversAt_factorizes _ .particleWave⟩

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
