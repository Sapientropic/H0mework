import H0mework.Versions.X.Fock.SourceHistory.PrimeClockResidualRegression

/-! Exact paired next occurrences feed the original prime transfer, full residual and same-root material consumer. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalTransfer SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem next_projection (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    primeProjection (nextAtom (process := process) jointRead current bound actor) =
      nextAtom (process := process) rawField current bound actor := by
  rw [SourceConditionalRecovery.nextAtom_is_observed_point, SourceConditionalRecovery.nextAtom_is_observed_point]
  exact projection_source (SourceOperationNative.point ((history current bound).stageAt actor).next)

theorem projected_transfer_recovers (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField current bound
      (Runtime.Actor.actorTransfer (process := process) rawField current bound
        (taskValue (historyPMF bound) (fun index => (sample current bound index : Nat))))
      (primeProjection (nextAtom (process := process) jointRead current bound actor)) =
        decodeClock (observe current bound actor) := by
  rw [next_projection]
  exact original_transfer_clock current bound actor

theorem joint_information_consumed (bound width : Nat) :
    let current := SourcePrimeObservationDelay.startRuntime sourceOwner bound width
    let stage := (history current bound).stageAt (Fin.last bound)
    (∀ index, type_of% (word_is_actual index) ∧ type_of% (primitive_replays_source index) ∧ type_of% (primitive_unit_mass index)) ∧
      (∀ left right : JointField, type_of% (fibre_exact left right)) ∧
      type_of% residual_fixed ∧ type_of% residual_not_source ∧ type_of% clock_not_projectable ∧
      (∀ sourceIndex, type_of% (finite_silence_not_complete_zero sourceIndex)) ∧
      (∀ actor : Fin (bound + 1), type_of% (query_material current bound actor) ∧
        type_of% (restored_model_actual current bound actor) ∧ type_of% (conditional_is_original current bound actor) ∧
        type_of% (next_projection current bound actor) ∧ type_of% (projected_transfer_recovers current bound actor)) ∧
      (∀ task : Fin (bound + 1) → ℂ,
        (∀ actor : Fin (bound + 1), type_of% (transfer_from_joint_conditional current bound task actor)) ∧
        type_of% (SourcePrimeObservationDelay.residuals_zero sourceOwner current bound task) ∧
        type_of% (Runtime.Actor.reconstruct_actor (process := process) rawField current bound (taskValue (historyPMF bound) task))) ∧
      type_of% (prime_loss_joint_recovery bound width) ∧
      queryModel (observe current bound (Fin.last bound)) =
        SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock stage.next ∧
      type_of% (SourceOperationNative.Observed.model_factorizes (process := process) jointRead (current.advance bound)) ∧
      type_of% (SourcePrimeObservationDelay.information_consumed bound width) := by
  exact ⟨(fun index => ⟨word_is_actual index, primitive_replays_source index, primitive_unit_mass index⟩),
    fibre_exact, residual_fixed, residual_not_source, clock_not_projectable, finite_silence_not_complete_zero,
    (fun actor => ⟨query_material _ bound actor, restored_model_actual _ bound actor, conditional_is_original _ bound actor,
      next_projection _ bound actor, projected_transfer_recovers _ bound actor⟩),
    (fun task => ⟨transfer_from_joint_conditional _ bound task,
      SourcePrimeObservationDelay.residuals_zero sourceOwner _ bound task,
      Runtime.Actor.reconstruct_actor (process := process) rawField _ bound (taskValue (historyPMF bound) task)⟩),
    prime_loss_joint_recovery bound width, query_model_actual _ bound (Fin.last bound),
    SourceOperationNative.Observed.model_factorizes (process := process) jointRead _,
    SourcePrimeObservationDelay.information_consumed bound width⟩

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
