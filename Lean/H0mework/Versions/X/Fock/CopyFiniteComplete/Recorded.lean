import H0mework.Versions.X.Fock.CopyFiniteComplete.Playback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCompleteGraph.completeUniform SourceCompleteGraph.completeMeasurable
  SourceCompleteGraph.completeBorel SourceCompleteGraph.completeT2 windowMeasurable

def recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace (inventoryBound runtime) (inventoryBound runtime) :=
  SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (completedRecord runtime)

def residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  target - SourceCopyGraph.action (inventoryBound runtime) index
    (fieldRead (inventoryBound runtime) (inventoryBound runtime) (recovery runtime index target))

theorem recovery_query (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    recovery runtime index = SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (query runtime) := by
  unfold recovery
  rw [completed_record, ← SourceFixedInventoryRecovery.complete_record]

theorem recovery_model (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    recovery runtime index = SourceConditionalGraphDecoder.fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) :=
  (recovery_query runtime index).trans (decoder_linear model runtime index).symm

theorem residual_query (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index target = SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index
      (query runtime) target := by
  rw [residual, recovery_query]
  have original := SourceConditionalGraphDecoder.original_reconstruction (inventoryBound runtime) (inventoryBound runtime) index
    (query runtime) target
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

theorem residual_model (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index target = SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index
      (Hilbert.read model (inventoryBound runtime)) target :=
  (residual_query runtime index target).trans (residual_value model runtime index target).symm

theorem reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime) (inventoryBound runtime) (recovery runtime index target)) +
        residual runtime index target = target := by
  rw [residual]
  exact add_sub_cancel _ _

theorem field_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    recovery runtime index (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)) = value := by
  rw [recovery_query]
  exact SourceGraphRefinement.complete_field_recovery runtime index value

theorem recorded_boundary_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    residual runtime index SourceCompleteGraph.boundary ≠ 0 := by
  rw [residual_query]
  exact finite_boundary_nonzero runtime index

end
end SourceFiniteCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
