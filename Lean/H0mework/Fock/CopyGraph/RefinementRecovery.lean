import H0mework.Fock.CopyGraph.RefinementTransfer
import H0mework.Fock.CopyGraph.CostPrice

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceConditionalGraphDecoder (action decode)
noncomputable section
universe u v
variable {Fine : Type u} [MeasurableSpace Fine] [MeasurableSingletonClass Fine]
variable {Coarse : Type v} [MeasurableSpace Coarse]

omit [MeasurableSingletonClass Fine] in
theorem prediction_update (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    action depth bound index fine (decode depth bound index fine value) =
      action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value) +
        gain depth bound index fine forget value := by
  change action depth bound index fine (decode depth bound index fine value) =
    action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value) +
      (action depth bound index fine (decode depth bound index fine value) -
        action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value))
  abel

theorem cost_decreases (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    ‖SourceConditionalGraphDecoder.residual depth bound index fine value‖ ^ 2 ≤
      ‖SourceConditionalGraphDecoder.residual depth bound index (forget ∘ fine) value‖ ^ 2 := by
  rw [residual_energy]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem no_gain_iff (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : SourceJointClockGraph.Carrier) :
    ‖SourceConditionalGraphDecoder.residual depth bound index (forget ∘ fine) value‖ ^ 2 =
      ‖SourceConditionalGraphDecoder.residual depth bound index fine value‖ ^ 2 ↔
        action depth bound index fine (decode depth bound index fine value) =
          action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value) := by
  rw [residual_energy]
  constructor
  · intro same
    have zero : ‖gain depth bound index fine forget value‖ ^ 2 = 0 := by linarith only [same]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp zero))
  · intro same
    have zero : gain depth bound index fine forget value = 0 := by
      change action depth bound index fine (decode depth bound index fine value) -
        action depth bound index (forget ∘ fine) (decode depth bound index (forget ∘ fine) value) = 0
      exact sub_eq_zero.mpr same
    rw [zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

variable [MeasurableSingletonClass Coarse]

theorem conditional_budget (depth bound : Nat) (index : Index depth) (fine : Fin (bound + 1) → Fine) (forget : Fine → Coarse)
    (value : Space (historyPMF bound)) :
    ‖residual (historyPMF bound) (forget ∘ fine) value‖ ^ 2 +
      SourceConditionalCorrection.strength depth bound index * ‖SourceConditionalCorrection.clockPair bound (forget ∘ fine) value‖ ^ 2 /
        SourceConditionalCorrection.denominator depth bound index (forget ∘ fine) =
      ‖residual (historyPMF bound) fine value‖ ^ 2 +
        SourceConditionalCorrection.strength depth bound index * ‖SourceConditionalCorrection.clockPair bound fine value‖ ^ 2 /
          SourceConditionalCorrection.denominator depth bound index fine +
      ‖gain depth bound index fine forget (SourceConditionalGraph.copyRead depth bound index value)‖ ^ 2 := by
  have generated := residual_energy depth bound index fine forget (SourceConditionalGraph.copyRead depth bound index value)
  rw [SourceConditionalCost.minimum_cost, SourceConditionalCost.minimum_cost] at generated
  exact generated

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
