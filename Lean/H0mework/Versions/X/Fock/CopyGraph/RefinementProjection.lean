import H0mework.Versions.X.Fock.CopyGraph.RefinementTransfer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (action decode inclusion sourceEquiv residual)
noncomputable section
universe u v
variable {Fine : Type u} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type v} [MeasurableSpace Coarse]
attribute [local instance] SourceConditionalGraphDecoder.imageComplete

theorem transfer_fine_prediction (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine)
    (forget : Fine → Coarse) (value : SourceJointClockGraph.Carrier) :
    IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index (forget ∘ fine)).range) (inclusion depth bound index (forget ∘ fine))
      (action depth bound index fine (decode depth bound index fine value)) =
    IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index (forget ∘ fine)).range) (inclusion depth bound index (forget ∘ fine)) value := by
  rw [coarse_transfer depth bound index fine forget (action depth bound index fine (decode depth bound index fine value))]
  rw [SourceConditionalGraphDecoder.encoded_decode, IsometricRetainedTransfer.transfer_pullback]
  exact (coarse_transfer depth bound index fine forget value).symm

theorem decode_fine_prediction (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine)
    (forget : Fine → Coarse) (value : SourceJointClockGraph.Carrier) :
    decode depth bound index (forget ∘ fine) (action depth bound index fine (decode depth bound index fine value)) =
      decode depth bound index (forget ∘ fine) value := by
  change (sourceEquiv depth bound index (forget ∘ fine)).symm
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index (forget ∘ fine)).range) (inclusion depth bound index (forget ∘ fine))
        (action depth bound index fine (decode depth bound index fine value))) =
    (sourceEquiv depth bound index (forget ∘ fine)).symm
      (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
        (Next := (action depth bound index (forget ∘ fine)).range) (inclusion depth bound index (forget ∘ fine)) value)
  exact congrArg (sourceEquiv depth bound index (forget ∘ fine)).symm (transfer_fine_prediction depth bound index fine forget value)

theorem gain_coarse_residual (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine)
    (forget : Fine → Coarse) (value : SourceJointClockGraph.Carrier) :
    gain depth bound index fine forget value =
      residual depth bound index (forget ∘ fine) (action depth bound index fine (decode depth bound index fine value)) := by
  have original := SourceConditionalGraphDecoder.reconstruction depth bound index (forget ∘ fine)
    (action depth bound index fine (decode depth bound index fine value))
  rw [decode_fine_prediction] at original
  exact (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans original)).symm

theorem gain_coarse_source (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine)
    (forget : Fine → Coarse)
    (value : SourceWeightedRecovery.Space (SourceWeightedRecovery.observed
      (SourceGeneratedRuntimeHistoryProbability.historyPMF bound) (forget ∘ fine))) :
    gain depth bound index fine forget (action depth bound index (forget ∘ fine) value) = 0 := by
  have lifted := congrArg (decode depth bound index fine) (action_lift depth bound index fine forget value)
  rw [SourceConditionalGraphDecoder.decode_action] at lifted
  change action depth bound index fine (decode depth bound index fine (action depth bound index (forget ∘ fine) value)) -
    action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) (action depth bound index (forget ∘ fine) value)) = 0
  rw [← lifted, action_lift, SourceConditionalGraphDecoder.decode_action, sub_self]

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
