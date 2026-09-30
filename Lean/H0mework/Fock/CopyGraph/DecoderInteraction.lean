import H0mework.Fock.CopyGraph.DecoderSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index scale)
open SourceConditionalGraph (copyRead)
open scoped InnerProductSpace
noncomputable section
universe u

theorem copy_inner (depth bound : Nat) (index : Index depth) (left right : Space (historyPMF bound)) :
    ⟪copyRead depth bound index left, copyRead depth bound index right⟫_ℂ =
      ⟪left, right⟫_ℂ +
        starRingEnd ℂ (SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound left)) *
          SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound right) +
        (scale depth index : ℂ) ^ 2 *
          (starRingEnd ℂ (SourceClockComplex.clock (SourceHistoryWord.word bound left)) *
            SourceClockComplex.clock (SourceHistoryWord.word bound right)) := by
  change inner ℂ
    (SourceCopyGraph.action depth index (SourceJointClockGraph.read (SourceHistoryWord.word bound left)))
    (SourceCopyGraph.action depth index (SourceJointClockGraph.read (SourceHistoryWord.word bound right))) = _
  rw [SourceCopyGraph.action_apply, SourceCopyGraph.action_apply, WithLp.prod_inner_apply]
  change inner ℂ (SourceCopyGraph.jointAction depth index (SourceMassCompletion.jointRead (SourceHistoryWord.word bound left)))
    (SourceCopyGraph.jointAction depth index (SourceMassCompletion.jointRead (SourceHistoryWord.word bound right))) +
      inner ℂ ((scale depth index : ℂ) * SourceClockComplex.clock (SourceHistoryWord.word bound left))
        ((scale depth index : ℂ) * SourceClockComplex.clock (SourceHistoryWord.word bound right)) = _
  rw [SourceCopyGraph.joint_apply, SourceCopyGraph.joint_apply, WithLp.prod_inner_apply]
  change inner ℂ (SourceCopyGraph.hilbertAction depth index (SourceSuccessorBoundary.readWord (SourceHistoryWord.word bound left)))
    (SourceCopyGraph.hilbertAction depth index (SourceSuccessorBoundary.readWord (SourceHistoryWord.word bound right))) +
      inner ℂ (SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound left))
        (SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word bound right)) + _ = _
  rw [(SourceCopyGraph.hilbertAction depth index).inner_map_map]
  have original : inner ℂ (SourceSuccessorBoundary.readWord (SourceHistoryWord.word bound left))
      (SourceSuccessorBoundary.readWord (SourceHistoryWord.word bound right)) = inner ℂ left right :=
    (SourceHistoryWord.hilbert bound).inner_map_map left right
  rw [original]
  simp only [RCLike.inner_apply, map_mul, map_natCast]
  ring

theorem conditional_inner {Observed : Type u} [MeasurableSpace Observed] [MeasurableSingletonClass Observed]
    (depth bound : Nat) (index : Index depth) (observer : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) (proposal : Space (observed (historyPMF bound) observer)) :
    ⟪action depth bound index observer proposal,
      copyRead depth bound index (SourceWeightedRecovery.residual (historyPMF bound) observer value)⟫_ℂ =
        (scale depth index : ℂ) ^ 2 *
          (starRingEnd ℂ (SourceClockComplex.clock (SourceHistoryWord.word bound (pullback (historyPMF bound) observer proposal))) *
            SourceClockComplex.clock (SourceHistoryWord.word bound (SourceWeightedRecovery.residual (historyPMF bound) observer value))) := by
  rw [action_source, copy_inner, IsometricRetainedTransfer.residual_orthogonal, SourceConditionalGraph.residual_mass]
  simp only [mul_zero, add_zero, zero_add]

theorem clock_prediction {Observed : Type u} [MeasurableSpace Observed]
    (bound : Nat) (observer : Fin (bound + 1) → Observed) :
    SourceClockComplex.clock (SourceHistoryWord.word bound
      (pullback (historyPMF bound) observer
        (transfer (historyPMF bound) observer (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound))))) =
      Real.sqrt (bound + 1 : ℝ) •
        (‖transfer (historyPMF bound) observer (taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound))‖ : ℂ) ^ 2 := by
  let value := taskValue (historyPMF bound) (SourceGeneratedJointClock.signal bound)
  have whole := IsometricRetainedTransfer.pullback_transfer_add_residual (pullback (historyPMF bound) observer) value
  have orthogonal := inner_eq_zero_symm.mp (IsometricRetainedTransfer.residual_orthogonal
    (pullback (historyPMF bound) observer) value (transfer (historyPMF bound) observer value))
  have pairing := congrArg (fun point : Space (historyPMF bound) =>
    inner ℂ point (pullback (historyPMF bound) observer (transfer (historyPMF bound) observer value))) whole
  rw [inner_add_left, orthogonal, add_zero, inner_self_eq_norm_sq_to_K,
    (pullback (historyPMF bound) observer).norm_map] at pairing
  rw [SourceConditionalGraph.clock_inner]
  exact congrArg (fun scalar : ℂ => Real.sqrt (bound + 1 : ℝ) • scalar) pairing.symm

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
