import H0mework.Versions.R2.Physics.Actual.HistoryOnShell
import H0mework.Versions.R2.Physics.SpinRuntime.RuntimeConsumer

/-! The weak source history is the configuration readout of the original
sealed inquiry runtime, including its complete registered prefix. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.History

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

theorem nativeCurrent_eq_visit (index : ℕ) :
    nativeCurrent index = (SpinPair.visit index).current := by
  induction index with
  | zero => rfl
  | succ index induction =>
      change SpinPair.next (nativeCurrent index) =
        SpinPair.next (SpinPair.visit index).current
      rw [induction]

theorem runtime_prefix (index : Fin 7) :
    (physicalInquiryRuntime.stateAt index.val).engine.node.erase =
      (SpinPair.historicalPresentation index).erase := by
  fin_cases index <;> rfl

private theorem next_erases_to_native
    (engine : Engine physicalInquiryProcess)
    (activation : Engine.SourceNativeInquiryActivationAt engine)
    (index : ℕ)
    (current : engine.node.erase = (SpinPair.readPresentation index).erase) :
    (engine.ask activation).next.node.erase =
      (SpinPair.readPresentation (index + 1)).erase := by
  rcases engine with ⟨state⟩
  have same : state = SpinPair.RuntimeState.native index :=
    SpinPair.runtimePresentation_erase_injective
      (current.trans (SpinPair.runtimePresentation_native_erase index).symm)
  subst state
  rcases index with _ | _ | _ | index <;> rfl

theorem runtime_suffix (index : ℕ) :
    (physicalInquiryRuntime.stateAt (index + 7)).engine.node.erase =
      (SpinPair.readPresentation index).erase := by
  induction index with
  | zero => rfl
  | succ index induction =>
      change ((physicalInquiryRuntime.stateAt (index + 7)).engine.ask
        (physicalInquiryRuntime.stateAt (index + 7)).activation).next.node.erase = _
      exact next_erases_to_native _ _ index induction

theorem configuration_add_seven_eq_runtime (index : ℕ) :
    configuration (index + 7) =
      materialConfiguration
        (SpinPair.support (SpinPair.visit (index + 1)).current) := by
  rw [configuration_add_seven, nativeCurrent_eq_visit]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9CU.History
