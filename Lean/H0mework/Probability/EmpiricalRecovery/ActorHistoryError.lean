import H0mework.Probability.EmpiricalRecovery.ActorHistoryCore

/-! Both the actor residual and the complete old history inventory enter terminal source recovery. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Runtime.Actor.History

open SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

local instance : MeasurableSpace (Field read) := fieldBorel read

theorem complete_error_decomposition (depth : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    let current := actorTransfer read runtime bound value
    let retained := SourceGeneratedEmpiricalHilbert.retainedHistory read runtime bound (depth + 1) current
    rawTerminalError read runtime bound depth task decoder =
      ‖actorResidual read runtime bound value‖ ^ 2 +
        SourceGeneratedEmpiricalHilbert.inventoryEnergy read runtime bound (depth + 1) retained.2 +
          SourceConditionalRecovery.decoderError read (runtime.advance depth) bound retained.1 decoder :=
  (rawTerminalError_before_field read runtime bound depth task decoder).trans
    ((congrArg (‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·)
      (SourceConditionalRecovery.History.terminalError_decomposition read runtime bound depth
        (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) decoder)).trans
          (add_assoc _ _ _).symm)

theorem complete_error_lower_bound (depth : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    let retained := SourceGeneratedEmpiricalHilbert.retainedHistory read runtime bound (depth + 1)
      (actorTransfer read runtime bound value)
    ‖actorResidual read runtime bound value‖ ^ 2 +
        SourceGeneratedEmpiricalHilbert.inventoryEnergy read runtime bound (depth + 1) retained.2 ≤
      rawTerminalError read runtime bound depth task decoder := by
  dsimp only
  rw [complete_error_decomposition]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun index _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

theorem complete_error_attains (depth : Nat) (task : Fin (bound + 1) → ℂ) :
    let value := taskValue (historyPMF bound) task
    let retained := SourceGeneratedEmpiricalHilbert.retainedHistory read runtime bound (depth + 1)
      (actorTransfer read runtime bound value)
    rawTerminalError read runtime bound depth task (fun atom => retained.1 atom) =
      ‖actorResidual read runtime bound value‖ ^ 2 +
        SourceGeneratedEmpiricalHilbert.inventoryEnergy read runtime bound (depth + 1) retained.2 :=
  (rawTerminalError_before_field read runtime bound depth task _).trans
    (congrArg (‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2 + ·)
      (SourceConditionalRecovery.History.terminalError_attains read runtime bound depth
        (actorTransfer read runtime bound (taskValue (historyPMF bound) task))))

theorem first_complete_loss_persists (depth : Nat) (task : Fin (bound + 1) → ℂ) (decoder : Field read → ℂ) :
    let value := taskValue (historyPMF bound) task
    ‖actorResidual read runtime bound value‖ ^ 2 +
        ‖SourceGeneratedEmpiricalHilbert.residual read runtime bound (actorTransfer read runtime bound value)‖ ^ 2 ≤
      rawTerminalError read runtime bound depth task decoder :=
  (add_le_add (le_refl (‖actorResidual read runtime bound (taskValue (historyPMF bound) task)‖ ^ 2))
    (SourceConditionalRecovery.History.first_loss_persists read runtime bound depth
      (actorTransfer read runtime bound (taskValue (historyPMF bound) task)) decoder)).trans_eq
      (rawTerminalError_before_field read runtime bound depth task decoder).symm

theorem complete_source_restored (depth : Nat) (value : ActorSpace bound) :
    actorPullback read runtime bound
        ((SourceGeneratedEmpiricalHilbert.retainedHistory read runtime bound depth).symm
          (SourceGeneratedEmpiricalHilbert.retainedHistory read runtime bound depth (actorTransfer read runtime bound value))) +
      actorResidual read runtime bound value = value :=
  (congrArg (fun current => actorPullback read runtime bound current + actorResidual read runtime bound value)
    ((SourceGeneratedEmpiricalHilbert.retainedHistory read runtime bound depth).symm_apply_apply _)).trans
      (IsometricRetainedTransfer.pullback_transfer_add_residual (actorPullback read runtime bound) value)

end
end SourceWeightedRecovery.Runtime.Actor.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
