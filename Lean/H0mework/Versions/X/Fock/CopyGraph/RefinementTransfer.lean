import H0mework.Versions.X.Fock.CopyGraph.RefinementImage
import H0mework.Realization.HilbertTransfer.Composition

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (action decode inclusion)
noncomputable section
universe u v
variable {Fine : Type u} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type v} [MeasurableSpace Coarse]
attribute [local instance] SourceConditionalGraphDecoder.imageComplete

def gain (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (action depth bound index fine).comp (decode depth bound index fine) -
    (action depth bound index (forget ∘ fine)).comp (decode depth bound index (forget ∘ fine))

theorem coarse_transfer (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
      (Next := (action depth bound index (forget ∘ fine)).range) (inclusion depth bound index (forget ∘ fine)) value =
        IsometricRetainedTransfer.transfer (Current := (action depth bound index fine).range)
          (Next := (action depth bound index (forget ∘ fine)).range) (imageLift depth bound index fine forget)
          (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
            (Next := (action depth bound index fine).range) (inclusion depth bound index fine) value) := by
  have generated := IsometricRetainedTransfer.transfer_comp (Source := SourceJointClockGraph.Carrier)
    (Mid := (action depth bound index fine).range) (Target := (action depth bound index (forget ∘ fine)).range)
    (inclusion depth bound index fine) (imageLift depth bound index fine forget)
  rw [inclusion_comp] at generated
  exact DFunLike.congr_fun generated value

theorem gain_is_added (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    gain depth bound index fine forget value = inclusion depth bound index fine
      (IsometricRetainedTransfer.residual (Current := (action depth bound index fine).range)
        (Next := (action depth bound index (forget ∘ fine)).range) (imageLift depth bound index fine forget)
        (IsometricRetainedTransfer.transfer (Current := SourceJointClockGraph.Carrier)
          (Next := (action depth bound index fine).range) (inclusion depth bound index fine) value)) := by
  change action depth bound index fine (decode depth bound index fine value) -
    action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value) = _
  rw [SourceConditionalGraphDecoder.encoded_decode, SourceConditionalGraphDecoder.encoded_decode, coarse_transfer]
  change inclusion depth bound index fine _ - inclusion depth bound index (forget ∘ fine) _ =
    inclusion depth bound index fine (_ - imageLift depth bound index fine forget _)
  rw [map_sub]
  rfl

theorem residual_update (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    SourceConditionalGraphDecoder.residual depth bound index (forget ∘ fine) value =
      SourceConditionalGraphDecoder.residual depth bound index fine value + gain depth bound index fine forget value := by
  have generated := IsometricRetainedTransfer.residual_comp (Source := SourceJointClockGraph.Carrier)
    (Mid := (action depth bound index fine).range) (Target := (action depth bound index (forget ∘ fine)).range)
    (inclusion depth bound index fine) (imageLift depth bound index fine forget) value
  rw [inclusion_comp, ← gain_is_added] at generated
  exact generated

theorem residual_energy (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    ‖SourceConditionalGraphDecoder.residual depth bound index (forget ∘ fine) value‖ ^ 2 =
      ‖SourceConditionalGraphDecoder.residual depth bound index fine value‖ ^ 2 + ‖gain depth bound index fine forget value‖ ^ 2 := by
  have generated := IsometricRetainedTransfer.residual_comp_energy (Source := SourceJointClockGraph.Carrier)
    (Mid := (action depth bound index fine).range) (Target := (action depth bound index (forget ∘ fine)).range)
    (inclusion depth bound index fine) (imageLift depth bound index fine forget) value
  rw [inclusion_comp] at generated
  rw [gain_is_added, (inclusion depth bound index fine).norm_map]
  unfold SourceConditionalGraphDecoder.residual
  with_reducible exact generated

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
