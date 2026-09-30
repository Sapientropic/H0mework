import H0mework.Fock.CopyGraph.NormalInverseObservation
import H0mework.Fock.CopyGraph.ColumnForcingRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceColumnForcing

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceFiniteCompleteGraph.windowMeasurable

def recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) : FieldSpace (inventoryBound runtime) (inventoryBound runtime) :=
  field (inventoryBound runtime) (inventoryBound runtime) index (SourceFiniteCompleteGraph.completedRecord runtime) target

theorem recovery_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    recovery runtime index target = SourceNormalInverse.recovery runtime index target :=
  field_source _ _ index _ target

theorem recovery_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    recovery runtime index target = field (inventoryBound runtime) (inventoryBound runtime) index
      (SourceFiniteCompleteGraph.nextRecord runtime) target := by
  rw [SourceFiniteCompleteGraph.next_record]
  rfl

theorem actual_field_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : FieldSpace (inventoryBound runtime) (inventoryBound runtime)) :
    recovery runtime index (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime) (inventoryBound runtime) value)) = value := by
  rw [recovery_source, SourceNormalInverse.recovery_source]
  exact SourceFiniteCompleteGraph.field_recovery runtime index value

theorem boundary_forcing_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    forcing (inventoryBound runtime) (inventoryBound runtime) index (SourceFiniteCompleteGraph.completedRecord runtime)
      (SourceNormalInverse.remaining runtime index SourceCompleteGraph.boundary) = 0 := by
  have actual := remaining_forcing_zero (inventoryBound runtime) (inventoryBound runtime) index
    (SourceFiniteCompleteGraph.completedRecord runtime) SourceCompleteGraph.boundary
  rw [remaining_source] at actual
  exact actual

theorem forcing_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    forcing (inventoryBound runtime) (inventoryBound runtime) index (SourceFiniteCompleteGraph.completedRecord runtime) 0 = 0 := by
  rw [forcing_source, map_zero]

theorem no_free_target (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    let query := SourceFiniteCompleteGraph.completedRecord runtime
    let hidden := SourceNormalInverse.remaining runtime index SourceCompleteGraph.boundary
    hidden ≠ 0 ∧
      forcing (inventoryBound runtime) (inventoryBound runtime) index query hidden =
        forcing (inventoryBound runtime) (inventoryBound runtime) index query 0 ∧
      recovery runtime index hidden = recovery runtime index 0 := by
  dsimp only
  have same := (boundary_forcing_zero runtime index).trans (forcing_zero runtime index).symm
  exact ⟨SourceNormalInverse.boundary_nonzero runtime index, same,
    (forcing_equal_iff _ _ index _ _ _).mp same⟩

theorem recovery_realization (round : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    let depth := inventoryBound runtime
    let copied := SourceCopyGraph.complexAction depth index
      (SourceGeneratedAcquisitionJoint.word depth depth (recovery runtime index target))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (SourceGeneratedAcquisitionJoint.sourceRound round copied))
      (inventoryBound (SourceGeneratedAcquisitionJoint.sourceRound round copied))
      (SourceGeneratedAcquisitionJoint.realizeWord round copied) +
        remaining depth depth index (SourceFiniteCompleteGraph.completedRecord runtime) target = target := by
  dsimp only
  rw [SourceCopyGraph.original_copy_realization]
  exact reconstruction _ _ index _ target

end
end SourceColumnForcing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
