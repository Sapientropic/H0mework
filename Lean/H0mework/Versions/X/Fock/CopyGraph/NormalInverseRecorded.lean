import H0mework.Versions.X.Fock.CopyGraph.NormalInverseField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNormalInverse

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceFiniteCompleteGraph.windowMeasurable

def recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    SourceJointClockGraph.Carrier →L[ℂ] FieldSpace (inventoryBound runtime) (inventoryBound runtime) :=
  fieldDecode (inventoryBound runtime) (inventoryBound runtime) index (SourceFiniteCompleteGraph.completedRecord runtime)

def remaining (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) : SourceJointClockGraph.Carrier :=
  residual (inventoryBound runtime) (inventoryBound runtime) index (SourceFiniteCompleteGraph.completedRecord runtime) target

theorem recovery_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    recovery runtime index = SourceFiniteCompleteGraph.recovery runtime index := by
  rw [recovery, field_decode_source]
  rfl

theorem remaining_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    remaining runtime index target = SourceFiniteCompleteGraph.residual runtime index target := by
  rw [remaining, residual_source, SourceFiniteCompleteGraph.residual_query]
  rw [SourceFiniteCompleteGraph.completed_record, ← SourceFixedInventoryRecovery.complete_record]

theorem recovery_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    recovery runtime index = fieldDecode (inventoryBound runtime) (inventoryBound runtime) index
      (SourceFiniteCompleteGraph.nextRecord runtime) := by
  rw [SourceFiniteCompleteGraph.next_record]
  rfl

theorem recorded_equation (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (target : SourceJointClockGraph.Carrier) :
    type_of% (decode_equation (inventoryBound runtime) (inventoryBound runtime) index
      (SourceFiniteCompleteGraph.completedRecord runtime) target) :=
  decode_equation _ _ index _ target

theorem boundary_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    remaining runtime index SourceCompleteGraph.boundary ≠ 0 := by
  rw [remaining_source]
  exact SourceFiniteCompleteGraph.recorded_boundary_nonzero runtime index

end
end SourceNormalInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
