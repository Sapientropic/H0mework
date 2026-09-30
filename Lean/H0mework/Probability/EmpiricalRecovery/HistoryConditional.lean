import H0mework.Probability.EmpiricalRecovery.HistoryError
import H0mework.Probability.EmpiricalRecovery.Model

/-! Every increment of the old inventory is computed by its complete conditional source fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.History

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceOperationNative.Observed

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {B : Type u} [AddCommGroup B] (read : process.State → B)
variable (runtime : LivingRuntimeState process) (bound : Nat)

theorem floor_increment_conditional (depth : Nat) (value : Space read runtime bound) :
    let current := runtime.advance depth
    let task := (retainedHistory read runtime bound depth value).1
    inventoryEnergy read runtime bound (depth + 1) (retainedHistory read runtime bound (depth + 1) value).2 =
      inventoryEnergy read runtime bound depth (retainedHistory read runtime bound depth value).2 +
        ∑ index : Fin (bound + 1), (historyPMF bound index).toReal *
          ‖task (fieldSample read current bound index) -
            conditionalValue read current bound task (nextAtom read current bound index)
              (nextAtom_supported read current bound index)‖ ^ 2 := by
  dsimp only
  have step := IsometricRetainedTransfer.Chain.floor_succ
    (H := fun stage => Space read (runtime.advance stage) bound)
    (stagePullback read runtime bound) depth value
  apply step.trans
  apply congrArg (inventoryEnergy read runtime bound depth (retainedHistory read runtime bound depth value).2 + ·)
  apply (transfer_attains read (runtime.advance depth) bound (retainedHistory read runtime bound depth value).1).symm.trans
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun estimate : ℂ => (historyPMF bound index).toReal *
    ‖(retainedHistory read runtime bound depth value).1 (fieldSample read (runtime.advance depth) bound index) - estimate‖ ^ 2)
    (transfer_at_atom read (runtime.advance depth) bound _ _ (nextAtom_supported read (runtime.advance depth) bound index))

theorem no_increment_iff_model (depth : Nat) (value : Space read runtime bound) :
    inventoryEnergy read runtime bound (depth + 1) (retainedHistory read runtime bound (depth + 1) value).2 =
        inventoryEnergy read runtime bound depth (retainedHistory read runtime bound depth value).2 ↔
      ∀ first second : Fin (bound + 1),
        modelPoint (process := process) read ((history (runtime.advance depth) bound).stageAt first).next =
          modelPoint (process := process) read ((history (runtime.advance depth) bound).stageAt second).next →
        (retainedHistory read runtime bound depth value).1 (fieldSample read (runtime.advance depth) bound first) =
          (retainedHistory read runtime bound depth value).1 (fieldSample read (runtime.advance depth) bound second) := by
  have step := IsometricRetainedTransfer.Chain.floor_succ
    (H := fun stage => Space read (runtime.advance stage) bound)
    (stagePullback read runtime bound) depth value
  apply (congrArg (· = inventoryEnergy read runtime bound depth
    (retainedHistory read runtime bound depth value).2) step).to_iff.trans
  apply add_eq_left.trans
  change ‖residual read (runtime.advance depth) bound (retainedHistory read runtime bound depth value).1‖ ^ 2 = 0 ↔ _
  rw [sq_eq_zero_iff, norm_eq_zero]
  exact zero_residual_iff_model read (runtime.advance depth) bound _

end
end SourceConditionalRecovery.History
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
