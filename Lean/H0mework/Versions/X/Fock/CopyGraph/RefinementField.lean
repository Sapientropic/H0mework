import H0mework.Versions.X.Fock.CopyGraph.RefinementRecovery
import H0mework.Versions.X.Fock.CopyGraph.DecoderField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (action decode fieldDecode)
noncomputable section
universe u v
variable {Fine : Type u} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type v} [MeasurableSpace Coarse]

omit [MeasurableSingletonClass Fine] in
theorem gain_original (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    gain depth bound index fine forget value =
      SourceCopyGraph.action depth index (fieldRead depth bound
        (fieldDecode depth bound index fine value - fieldDecode depth bound index (forget ∘ fine) value)) := by
  rw [map_sub, map_sub]
  change action depth bound index fine (decode depth bound index fine value) -
    action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value) =
    SourceCopyGraph.action depth index (fieldRead depth bound (SourceConditionalGraphDecoder.realizeObserved depth bound fine
      (decode depth bound index fine value))) -
    SourceCopyGraph.action depth index (fieldRead depth bound (SourceConditionalGraphDecoder.realizeObserved depth bound (forget ∘ fine)
      (decode depth bound index (forget ∘ fine) value)))
  rw [SourceConditionalGraphDecoder.realized_action, SourceConditionalGraphDecoder.realized_action]

theorem original_error_gain (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : FieldSpace depth bound) :
    let target := SourceCopyGraph.action depth index (fieldRead depth bound value)
    ‖SourceCopyGraph.action depth index (fieldRead depth bound (value - fieldDecode depth bound index (forget ∘ fine) target))‖ ^ 2 =
      ‖SourceCopyGraph.action depth index (fieldRead depth bound (value - fieldDecode depth bound index fine target))‖ ^ 2 +
        ‖SourceCopyGraph.action depth index (fieldRead depth bound
          (fieldDecode depth bound index fine target - fieldDecode depth bound index (forget ∘ fine) target))‖ ^ 2 := by
  have generated := residual_energy depth bound index fine forget (SourceCopyGraph.action depth index (fieldRead depth bound value))
  rw [SourceConditionalGraphDecoder.original_residual, SourceConditionalGraphDecoder.original_residual, gain_original] at generated
  exact generated

omit [MeasurableSingletonClass Fine] in
theorem gain_realization (round depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    let gained := fieldDecode depth bound index fine value - fieldDecode depth bound index (forget ∘ fine) value
    let copied := SourceCopyGraph.complexAction depth index (word depth bound gained)
    fieldRead (SourceGeneratedAcquisitionJoint.depth (sourceRound round copied))
      (SourceGeneratedAcquisitionContinuation.inventoryBound (sourceRound round copied)) (realizeWord round copied) =
        gain depth bound index fine forget value := by
  exact (SourceCopyGraph.original_copy_realization round depth bound index _).trans
    (gain_original depth bound index fine forget value).symm

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
