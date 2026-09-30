import H0mework.Fock.CopyGraph.TemporalAcquisitionEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyTimeGram (model decode residual)
open SourceCopyTimeModel (finitePhases modelStep modelPoint)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem model_zero (depth : Nat) (index : Index depth) : model depth index 0 = 0 := by
  simpa only [map_zero] using SourceCopyTimeGram.model_source depth index (0 : SourceJointClockGraph.Carrier)

theorem field_model_next (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    let target := SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)
    model (inventoryBound runtime) index (finitePhases runtime index (steps + 1) (SourceJointClockGraph.action target)) =
      modelStep (inventoryBound runtime) index (model (inventoryBound runtime) index (finitePhases runtime index (steps + 1) target)) +
      modelPoint (inventoryBound runtime) index (decode (inventoryBound runtime) index
        (SourceCopyTimeModel.next (inventoryBound runtime) index
          (WithLp.ofLp (residual (inventoryBound runtime) index (finitePhases runtime index (steps + 1) target))))) := by
  have actual := SourceCopyTemporalBoundary.actual_model_next runtime index (steps + 1)
    (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value))
  rw [field_boundary_closed] at actual
  simpa only [SourceCopyTemporalBoundary.lastCell, Pi.single_zero, model_zero, add_zero] using actual

theorem material_consumed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    type_of% (SourceGraphRecurrence.material_history_step runtime index steps) ∧
      type_of% (field_boundary_closed runtime index steps value) ∧ type_of% (field_model_next runtime index steps value) ∧
      type_of% (SourceRecordedEvolution.history_energy runtime index (steps + 1)
        (SourceCopyTimeModel.time (SourceCopyProgram.scale (inventoryBound runtime) index)
          (SourceCopyGraph.action (inventoryBound runtime) index
            (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)))) := by
  with_reducible exact ⟨SourceGraphRecurrence.material_history_step runtime index steps,
    field_boundary_closed runtime index steps value, field_model_next runtime index steps value,
    SourceRecordedEvolution.history_energy runtime index (steps + 1) _⟩

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
