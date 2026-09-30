import H0mework.Versions.X.Fock.CopyGraph.DecoderMinimum

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

theorem decode_residual (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : SourceJointClockGraph.Carrier) :
    decode depth bound index query (residual depth bound index query value) = 0 := by
  have source := congrArg (decode depth bound index query) (reconstruction depth bound index query value)
  rw [map_add, decode_action] at source
  exact add_left_cancel (source.trans (add_zero _).symm)

theorem residual_of_source_orthogonal (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : SourceJointClockGraph.Carrier)
    (orthogonal : ∀ data : Space (observed (historyPMF bound) query), inner ℂ (action depth bound index query data) value = 0) :
    residual depth bound index query value = value := by
  have source := reconstruction depth bound index query value
  have pair := congrArg (inner ℂ (action depth bound index query (decode depth bound index query value))) source
  rw [inner_add_right, source_orthogonal, add_zero, orthogonal] at pair
  have vanished : action depth bound index query (decode depth bound index query value) = 0 := inner_self_eq_zero.mp pair
  rw [vanished, zero_add] at source
  exact source

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
