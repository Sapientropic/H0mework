import H0mework.Versions.X.Fock.CopyGraph.DecoderMinimum

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index scale)
open SourceConditionalGraph (copyRead)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

theorem conditional_gain (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖copyRead depth bound index (SourceWeightedRecovery.residual (historyPMF bound) observer value)‖ ^ 2 =
      ‖residual depth bound index observer (copyRead depth bound index value)‖ ^ 2 +
        ‖action depth bound index observer
          (decode depth bound index observer (copyRead depth bound index value) - transfer (historyPMF bound) observer value)‖ ^ 2 := by
  have generated := error_decomposition depth bound index observer (copyRead depth bound index value)
    (transfer (historyPMF bound) observer value)
  rw [action_source, ← map_sub] at generated
  exact generated

theorem every_decoder_retained_lower (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) (proposal : Space (observed (historyPMF bound) observer)) :
    ‖SourceWeightedRecovery.residual (historyPMF bound) observer value‖ ^ 2 ≤
      ‖copyRead depth bound index value - action depth bound index observer proposal‖ ^ 2 := by
  rw [action_source, ← map_sub, SourceConditionalGraph.copy_read_energy]
  have original := IsometricRetainedTransfer.decoder_error_decomposition (pullback (historyPMF bound) observer) value proposal
  have massCost := sq_nonneg ‖SourceSuccessorBoundary.mass ℂ
    (SourceHistoryWord.word bound (value - pullback (historyPMF bound) observer proposal))‖
  have clockCost := mul_nonneg (sq_nonneg (scale depth index : ℝ))
    (sq_nonneg ‖SourceClockComplex.clock (SourceHistoryWord.word bound (value - pullback (historyPMF bound) observer proposal))‖)
  nlinarith only [original, sq_nonneg ‖transfer (historyPMF bound) observer value - proposal‖, massCost, clockCost]

theorem retained_lower (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖SourceWeightedRecovery.residual (historyPMF bound) observer value‖ ^ 2 ≤
      ‖residual depth bound index observer (copyRead depth bound index value)‖ ^ 2 := by
  have paid := every_decoder_retained_lower depth bound index observer value
    (decode depth bound index observer (copyRead depth bound index value))
  rw [minimum_cost] at paid
  exact paid

theorem conditional_upper (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    ‖residual depth bound index observer (copyRead depth bound index value)‖ ^ 2 ≤
      ‖copyRead depth bound index (SourceWeightedRecovery.residual (historyPMF bound) observer value)‖ ^ 2 := by
  have candidate := decoder_lower depth bound index observer (copyRead depth bound index value)
    (transfer (historyPMF bound) observer value)
  rw [action_source, ← map_sub] at candidate
  exact candidate

theorem recovery_zero_iff (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    residual depth bound index observer (copyRead depth bound index value) = 0 ↔
      SourceWeightedRecovery.residual (historyPMF bound) observer value = 0 := by
  constructor
  · intro zero
    have paid := retained_lower depth bound index observer value
    rw [zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at paid
    apply norm_eq_zero.mp
    nlinarith only [paid, norm_nonneg (SourceWeightedRecovery.residual (historyPMF bound) observer value)]
  · intro zero
    have paid := conditional_upper depth bound index observer value
    rw [zero, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at paid
    apply norm_eq_zero.mp
    nlinarith only [paid, norm_nonneg (residual depth bound index observer (copyRead depth bound index value))]

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
