import H0mework.Versions.X.Fock.CopyGraph.RefinementSource
import H0mework.Versions.X.Fock.CopyGraph.DecoderInverse

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (action)
noncomputable section
universe u v
variable {Fine : Type u} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type v} [MeasurableSpace Coarse]

def imageLift (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse) :
    (action depth bound index (forget ∘ fine)).range →ₗᵢ[ℂ] (action depth bound index fine).range where
  toLinearMap := Submodule.inclusion (image_inclusion depth bound index fine forget)
  norm_map' _ := rfl

theorem inclusion_comp (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse) :
    (SourceConditionalGraphDecoder.inclusion depth bound index fine).comp (imageLift depth bound index fine forget) =
      SourceConditionalGraphDecoder.inclusion depth bound index (forget ∘ fine) := by
  apply LinearIsometry.ext
  intro value
  rfl

theorem image_lift_source (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : Space (observed (historyPMF bound) (forget ∘ fine))) :
    imageLift depth bound index fine forget (SourceConditionalGraphDecoder.sourceEquiv depth bound index (forget ∘ fine) value) =
      SourceConditionalGraphDecoder.sourceEquiv depth bound index fine (lift bound fine forget value) := by
  apply Subtype.ext
  exact (action_lift depth bound index fine forget value).symm

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
