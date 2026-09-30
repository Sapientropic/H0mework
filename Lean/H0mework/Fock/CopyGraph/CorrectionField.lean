import H0mework.Fock.CopyGraph.CorrectionRecovery
import H0mework.Fock.CopyGraph.DecoderField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedJointClockGraph SourceGeneratedAcquisitionJoint
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def fieldRecovery (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    FieldSpace depth bound →L[ℂ] FieldSpace depth bound :=
  (Actor.currentTransfer depth bound).comp
    ((pullback (historyPMF bound) query).toContinuousLinearMap.comp
      ((recovery depth bound index query).comp (Actor.currentPullback depth bound).toContinuousLinearMap))

variable [MeasurableSingletonClass Observed]

theorem field_recovery_original (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    fieldRecovery depth bound index query value = SourceConditionalGraphDecoder.fieldDecode depth bound index query
      (SourceCopyGraph.action depth index (fieldRead depth bound value)) := by
  change Actor.currentTransfer depth bound (pullback (historyPMF bound) query
    (recovery depth bound index query (Actor.currentPullback depth bound value))) = _
  rw [recovery_source]
  rfl

theorem original_minimum (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    fieldRecovery depth bound index query value ∈ Set.range (SourceConditionalGraphDecoder.realizeObserved depth bound query) ∧
      IsMinOn (fun proposal : FieldSpace depth bound =>
        ‖SourceCopyGraph.action depth index (fieldRead depth bound value) - SourceCopyGraph.action depth index (fieldRead depth bound proposal)‖ ^ 2)
        (Set.range (SourceConditionalGraphDecoder.realizeObserved depth bound query)) (fieldRecovery depth bound index query value) := by
  rw [field_recovery_original]
  exact SourceConditionalGraphDecoder.original_minimum depth bound index query _

theorem original_residual (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : FieldSpace depth bound) :
    SourceConditionalGraphDecoder.residual depth bound index query
      (SourceCopyGraph.action depth index (fieldRead depth bound value)) =
        SourceCopyGraph.action depth index (fieldRead depth bound (value - fieldRecovery depth bound index query value)) := by
  rw [field_recovery_original]
  exact SourceConditionalGraphDecoder.original_residual depth bound index query value

theorem original_residual_realization (round depth bound : Nat) (index : Index depth)
    (query : Fin (bound + 1) → Observed) (value : FieldSpace depth bound) :
    let copied := SourceCopyGraph.complexAction depth index (word depth bound (value - fieldRecovery depth bound index query value))
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        SourceConditionalGraphDecoder.residual depth bound index query (SourceCopyGraph.action depth index (fieldRead depth bound value)) := by
  rw [field_recovery_original]
  exact SourceConditionalGraphDecoder.original_residual_realization round depth bound index query value

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
