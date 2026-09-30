import H0mework.Probability.EmpiricalRecovery.FiniteTransfer
import H0mework.Probability.EmpiricalRecovery.FiniteMean

/-! The finite decoder retains both original information residuals and attains their exact total cost. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionObservationHistory.FiniteRecurrence.Native

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer SourceWeightedRecovery

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (windowBound : Nat) (runtime : LivingRuntimeState process) (actorBound : Nat)
variable (coefficients : Fin (windowBound + 1) → ℤ)
variable (sourceLaw : (SourceOperationNative.observer process read).comp
    (SourceOperationNative.sourceAction process ^ (windowBound + 1)) =
      ∑ index : Fin (windowBound + 1), coefficients index •
        stageEvaluator (SourceOperationNative.sourceAction process) (SourceOperationNative.observer process read) index.val)

include sourceLaw

theorem finite_error_decomposition (task : Fin (actorBound + 1) → ℂ) (decoder : (Fin (windowBound + 1) → B) → ℂ) :
    let value := taskValue (historyPMF actorBound) task
    error (historyPMF actorBound) (query read windowBound runtime actorBound) task decoder =
      ‖Runtime.Actor.actorResidual read runtime actorBound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime actorBound (Runtime.Actor.actorTransfer read runtime actorBound value)‖ ^ 2 +
          error (historyPMF actorBound) (query read windowBound runtime actorBound)
            (fun index => mean read windowBound runtime actorBound task (query read windowBound runtime actorBound index)) decoder := by
  dsimp only
  rw [finiteError_is_original, Runtime.Actor.actor_error_decomposition]
  congr 1
  unfold SourceConditionalRecovery.decoderError error
  apply Finset.sum_congr rfl
  intro index _
  dsimp only
  rw [fieldRead_query, completeTransfer_finite read windowBound runtime actorBound coefficients sourceLaw,
    mean_at_query]

theorem finite_attains (task : Fin (actorBound + 1) → ℂ) :
    let value := taskValue (historyPMF actorBound) task
    error (historyPMF actorBound) (query read windowBound runtime actorBound) task
        (mean read windowBound runtime actorBound task) =
      ‖Runtime.Actor.actorResidual read runtime actorBound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime actorBound (Runtime.Actor.actorTransfer read runtime actorBound value)‖ ^ 2 := by
  rw [finite_error_decomposition read windowBound runtime actorBound coefficients sourceLaw]
  simp only [error, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]

theorem finite_lower_bound (task : Fin (actorBound + 1) → ℂ) (decoder : (Fin (windowBound + 1) → B) → ℂ) :
    let value := taskValue (historyPMF actorBound) task
    ‖Runtime.Actor.actorResidual read runtime actorBound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime actorBound (Runtime.Actor.actorTransfer read runtime actorBound value)‖ ^ 2 ≤
      error (historyPMF actorBound) (query read windowBound runtime actorBound) task decoder := by
  rw [finite_error_decomposition read windowBound runtime actorBound coefficients sourceLaw]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun index _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

end
end SourceGeneratedActionObservationHistory.FiniteRecurrence.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
