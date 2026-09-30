import H0mework.Fock.CopyGraph.DecoderField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalGraphDecoder (action decode reconstruction source_orthogonal)
open SourceCopyProgram (Index)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def correction (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) : Space (observed (historyPMF bound) query) :=
  decode depth bound index query (SourceConditionalGraph.copyRead depth bound index value) - transfer (historyPMF bound) query value

theorem normal (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    (action depth bound index query).adjoint (target - action depth bound index query (decode depth bound index query target)) = 0 := by
  apply ext_inner_left ℂ
  intro proposal
  rw [inner_zero_right, ContinuousLinearMap.adjoint_inner_right]
  have remaining : target - action depth bound index query (decode depth bound index query target) =
      SourceConditionalGraphDecoder.residual depth bound index query target :=
    (eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (reconstruction depth bound index query target))).symm
  rw [remaining]
  exact source_orthogonal depth bound index query target proposal

theorem source_equation (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    (action depth bound index query).adjoint (action depth bound index query (correction depth bound index query value)) =
      (action depth bound index query).adjoint
        (SourceConditionalGraph.copyRead depth bound index (residual (historyPMF bound) query value)) := by
  have original := normal depth bound index query (SourceConditionalGraph.copyRead depth bound index value)
  rw [map_sub, sub_eq_zero] at original
  have remaining : SourceConditionalGraph.copyRead depth bound index (residual (historyPMF bound) query value) =
      SourceConditionalGraph.copyRead depth bound index value - action depth bound index query (transfer (historyPMF bound) query value) := by
    rw [SourceConditionalGraphDecoder.action_source, ← map_sub]
    rfl
  rw [remaining, map_sub]
  unfold correction
  rw [map_sub, map_sub, original]

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
