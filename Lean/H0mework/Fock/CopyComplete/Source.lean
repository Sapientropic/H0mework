import H0mework.Fock.CopyGraph.RecurrenceObservation
import H0mework.Fock.HistoryModel.WordsDynamicHilbertConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceCopyProgram (Index)
noncomputable section
local instance completeUniform (model : Nat) : UniformSpace (Complete.Carrier model) := Hilbert.uniform model
local instance completeMeasurable (model : Nat) : MeasurableSpace (Complete.Carrier model) := Hilbert.measurable model
local instance completeBorel (model : Nat) : BorelSpace (Complete.Carrier model) := ⟨rfl⟩
local instance completeT2 (model : Nat) : T2Space (Complete.Carrier model) := Hilbert.field_t2 model

theorem source_recovery (model depth bound : Nat) (index : Index depth) (value : Space (historyPMF bound)) :
    SourceConditionalGraphDecoder.residual depth bound index (Hilbert.read model bound)
      (SourceConditionalGraph.copyRead depth bound index value) = 0 :=
  (SourceConditionalGraphDecoder.recovery_zero_iff depth bound index (Hilbert.read model bound) value).mpr
    (Hilbert.complete_residual_zero model bound value)

theorem field_recovery (model depth bound : Nat) (index : Index depth) (value : FieldSpace depth bound) :
    SourceConditionalGraphDecoder.fieldDecode depth bound index (Hilbert.read model bound)
      (SourceCopyGraph.action depth index (fieldRead depth bound value)) = value := by
  apply (SourceGeneratedActionWords.Fock.OriginalHilbert.Actor.currentPullback depth bound).injective
  apply SourceGraphBirth.copy_read_injective depth bound index
  have reconstruction := SourceConditionalGraphDecoder.original_reconstruction depth bound index
    (Hilbert.read model bound) (SourceCopyGraph.action depth index (fieldRead depth bound value))
  have remaining := source_recovery model depth bound index
    (SourceGeneratedActionWords.Fock.OriginalHilbert.Actor.currentPullback depth bound value)
  change SourceConditionalGraphDecoder.residual depth bound index (Hilbert.read model bound)
    (SourceCopyGraph.action depth index (fieldRead depth bound value)) = 0 at remaining
  rw [remaining, add_zero] at reconstruction
  exact reconstruction

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
