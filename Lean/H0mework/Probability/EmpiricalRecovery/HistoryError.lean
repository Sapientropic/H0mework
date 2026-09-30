import H0mework.Probability.EmpiricalRecovery.HistorySamples
import H0mework.Probability.Empirical.Error

/-! Every raw terminal decoder pays exactly the old complete inventory plus its remaining estimation error. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.History

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

theorem terminalError_decomposition (depth : Nat) (value : Space read runtime bound) (decoder : Field read → ℂ) :
    terminalError read runtime bound depth value decoder =
      inventoryEnergy read runtime bound (depth + 1) (retainedHistory read runtime bound (depth + 1) value).2 +
        decoderError read (runtime.advance depth) bound (retainedHistory read runtime bound (depth + 1) value).1 decoder :=
  (terminalError_eq_norm read runtime bound depth value decoder).trans
    ((IsometricRetainedTransfer.Chain.terminal_error
      (H := fun stage => Space read (runtime.advance stage) bound)
      (stagePullback read runtime bound) (depth + 1) value _).trans
        (congrArg (inventoryEnergy read runtime bound (depth + 1)
          (retainedHistory read runtime bound (depth + 1) value).2 + ·)
          (decoderError_eq_norm read (runtime.advance depth) bound _ decoder).symm))

theorem terminalError_lower_bound (depth : Nat) (value : Space read runtime bound) (decoder : Field read → ℂ) :
    inventoryEnergy read runtime bound (depth + 1) (retainedHistory read runtime bound (depth + 1) value).2 ≤
      terminalError read runtime bound depth value decoder := by
  rw [terminalError_decomposition]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun index _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

theorem terminalError_attains (depth : Nat) (value : Space read runtime bound) :
    terminalError read runtime bound depth value
        (fun atom => (retainedHistory read runtime bound (depth + 1) value).1 atom) =
      inventoryEnergy read runtime bound (depth + 1) (retainedHistory read runtime bound (depth + 1) value).2 := by
  have selfError (current : LivingRuntimeState process) (estimate : Space read current.tick.next bound) :
      decoderError read current bound estimate (fun atom => estimate atom) = 0 := by
    simp [decoderError]
  exact (terminalError_decomposition read runtime bound depth value _).trans
    ((congrArg (inventoryEnergy read runtime bound (depth + 1)
      (retainedHistory read runtime bound (depth + 1) value).2 + ·)
      (selfError (runtime.advance depth) _)).trans (add_zero _))

theorem first_loss_persists (depth : Nat) (value : Space read runtime bound) (decoder : Field read → ℂ) :
    ‖residual read runtime bound value‖ ^ 2 ≤ terminalError read runtime bound depth value decoder := by
  have grows := IsometricRetainedTransfer.Chain.floor_monotone
    (H := fun stage => Space read (runtime.advance stage) bound)
    (stagePullback read runtime bound) value (show 1 ≤ depth + 1 by omega)
  have first : inventoryEnergy read runtime bound 1 (retainedHistory read runtime bound 1 value).2 =
      ‖residual read runtime bound value‖ ^ 2 := zero_add _
  exact first.symm.trans_le (grows.trans (terminalError_lower_bound read runtime bound depth value decoder))

end
end SourceConditionalRecovery.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
