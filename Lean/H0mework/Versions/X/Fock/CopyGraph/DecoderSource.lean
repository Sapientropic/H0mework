import H0mework.Versions.X.Fock.CopyGraph.ConditionalGeometry
import H0mework.Versions.X.Fock.SourceHistoryClock.DecoderFiniteSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index scale)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def action (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    Space (observed (historyPMF bound) observer) →L[ℂ] SourceJointClockGraph.Carrier :=
  (SourceCopyGraph.action depth index).comp ((SourceJointFiniteDecoder.read bound).comp
    (pullback (historyPMF bound) observer).toContinuousLinearMap)

theorem action_source (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) observer)) :
    action depth bound index observer value =
      SourceConditionalGraph.copyRead depth bound index (pullback (historyPMF bound) observer value) := by
  change SourceCopyGraph.action depth index
    (SourceJointFiniteDecoder.read bound (pullback (historyPMF bound) observer value)) = _
  rw [SourceJointFiniteDecoder.read_source]
  rfl

theorem source_norm_le (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) observer)) :
    ‖value‖ ≤ ‖action depth bound index observer value‖ := by
  have energy := SourceConditionalGraph.copy_read_energy depth bound index (pullback (historyPMF bound) observer value)
  rw [(pullback (historyPMF bound) observer).norm_map] at energy
  rw [action_source]
  have massCost := sq_nonneg ‖SourceSuccessorBoundary.mass ℂ
    (SourceHistoryWord.word bound (pullback (historyPMF bound) observer value))‖
  have clockCost := mul_nonneg (sq_nonneg (scale depth index : ℝ))
    (sq_nonneg ‖SourceClockComplex.clock (SourceHistoryWord.word bound (pullback (historyPMF bound) observer value))‖)
  nlinarith only [energy, massCost, clockCost, norm_nonneg value,
    norm_nonneg (SourceConditionalGraph.copyRead depth bound index (pullback (historyPMF bound) observer value))]

theorem source_antilipschitz (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    AntilipschitzWith 1 (action depth bound index observer) :=
  (action depth bound index observer).antilipschitz_of_bound
    (by intro value; simpa only [NNReal.coe_one, one_mul] using source_norm_le depth bound index observer value)

theorem source_injective (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    Function.Injective (action depth bound index observer) :=
  (source_antilipschitz depth bound index observer).injective

theorem source_closed_range (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed) :
    IsClosed (Set.range (action depth bound index observer)) :=
  (source_antilipschitz depth bound index observer).isClosed_range
    (action depth bound index observer).uniformContinuous

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
