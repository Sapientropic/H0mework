import H0mework.Versions.AB.Chemistry.LAlanineReentry.RuntimeRuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem reentryRuntime_parent_history (runtime : LivingRuntimeState reentryRuntimeProcess) :
    type_of% (reentryRuntime_history_installed runtime.tick.next) ∧
    type_of% reentrySourceHistory_actual ∧
    (reentrySourceHistory.2.1.realized, reentrySourceHistory.2.1.inheritedResidual,
      reentrySourceHistory.2.1.newNumericalResidual, reentrySourceHistory.2.1.totalRealizationResidual) =
        reentryParentRealization := ⟨reentryRuntime_history_installed runtime.tick.next, reentrySourceHistory_actual, rfl⟩

theorem reentryRuntime_entire_error_inherited (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryResponse runtime.state.current).inheritedResidual =
      JointNext.Math.electronicAdvance Source.hamiltonian Producer.sourceHamiltonian_hermitian
        (Continuation.duration : ℝ) Source.crossMatrix reentryParentResidual ∧
    ‖(reentryResponse runtime.state.current).inheritedResidual‖ = ‖reentryParentResidual‖ := by
  rw [reentryRuntime_response]
  exact ⟨rfl, Producer.inherited_error_exact⟩

theorem reentryRuntime_inherits_both_parent_errors (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryResponse runtime.state.current).inheritedResidual =
      JointNext.Math.electronicAdvance Source.hamiltonian Producer.sourceHamiltonian_hermitian
        (Continuation.duration : ℝ) Source.crossMatrix
        (reentryParentResult.inheritedResidual + reentryParentResult.newNumericalResidual) := by
  rw [(reentryRuntime_entire_error_inherited runtime).1]
  change JointNext.Math.electronicAdvance _ _ _ _ JointNext.Producer.totalRealizationResidual =
    JointNext.Math.electronicAdvance _ _ _ _ (JointNext.Producer.inheritedResidual + JointNext.Producer.newNumericalResidual)
  rw [JointNext.Producer.total_error_reconstruction.1]

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
