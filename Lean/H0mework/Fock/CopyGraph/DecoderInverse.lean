import H0mework.Fock.CopyGraph.DecoderSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

local instance imageComplete (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    CompleteSpace (action depth bound index observer).range :=
  (source_antilipschitz depth bound index observer).completeSpace_range_clm

def inclusion (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    (action depth bound index observer).range →ₗᵢ[ℂ] SourceJointClockGraph.Carrier :=
  (action depth bound index observer).range.subtypeₗᵢ

def sourceEquiv (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    Space (observed (historyPMF bound) observer) ≃L[ℂ] (action depth bound index observer).range :=
  (action depth bound index observer).equivRange (source_injective depth bound index observer)
    (source_closed_range depth bound index observer)

def decode (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] Space (observed (historyPMF bound) observer) :=
  (sourceEquiv depth bound index observer).symm.toContinuousLinearMap.comp
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index observer).range) (inclusion depth bound index observer))

def residual (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  IsometricRetainedTransfer.residual (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index observer).range) (inclusion depth bound index observer)

theorem source_equiv_value (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) observer)) :
    inclusion depth bound index observer (sourceEquiv depth bound index observer value) =
      action depth bound index observer value := rfl

theorem decode_action (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) observer)) :
    decode depth bound index observer (action depth bound index observer value) = value := by
  rw [← source_equiv_value]
  change (sourceEquiv depth bound index observer).symm
    (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index observer).range) (inclusion depth bound index observer)
      (inclusion depth bound index observer (sourceEquiv depth bound index observer value))) = value
  rw [IsometricRetainedTransfer.transfer_pullback, ContinuousLinearEquiv.symm_apply_apply]

theorem encoded_decode (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    action depth bound index observer (decode depth bound index observer target) =
      inclusion depth bound index observer (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index observer).range) (inclusion depth bound index observer) target) := by
  rw [← source_equiv_value]
  change inclusion depth bound index observer ((sourceEquiv depth bound index observer)
    ((sourceEquiv depth bound index observer).symm
      (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index observer).range) (inclusion depth bound index observer) target))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem reconstruction (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    action depth bound index observer (decode depth bound index observer target) + residual depth bound index observer target = target := by
  rw [encoded_decode]
  change _ + (target - _) = target
  exact add_sub_cancel _ _

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
