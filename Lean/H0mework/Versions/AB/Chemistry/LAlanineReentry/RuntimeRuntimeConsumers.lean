import H0mework.Versions.AB.Chemistry.LAlanineReentry.RuntimeRuntimeReadouts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem reentryRuntime_nuclearCertificate : Producer.nuclearClosure := reentryRuntime_sourceCertificate.2.1

theorem reentryRuntime_actualBody (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryCurrentPacket runtime.tick.next.state.current = Source.stepReadout.nuclear ∧
    reentryFrame runtime.tick.next.state.current = Source.stepReadout.nuclear.target ∧
    reentryCurrentLedger runtime.tick.next.state.current = Source.stepReadout.nuclear.targetLedger := by
  change (reentryResponse runtime.state.current).nuclear = _ ∧ (reentryResponse runtime.state.current).nuclear.target = _ ∧
    (reentryResponse runtime.state.current).nuclear.targetLedger = _
  rw [reentryRuntime_response]
  exact ⟨rfl, rfl, rfl⟩

theorem reentryRuntime_actualPhase (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryFrame runtime.tick.next.state.current).phase =
      Inertia.Mechanics.addResidual Producer.nuclearReference Producer.nuclearResidual := by
  rw [(reentryRuntime_actualBody runtime).2.1]
  exact Producer.nuclearPhase_reconstruction

theorem reentryRuntime_actualMovement (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryFrame runtime.tick.next.state.current).position ≠ reentryParentFrame.position ∧
    (reentryFrame runtime.tick.next.state.current).momentum ≠ reentryParentFrame.momentum := by
  rw [(reentryRuntime_actualBody runtime).2.1]
  exact ⟨Producer.nuclearPosition_changed, Producer.nuclearMomentum_changed⟩

theorem reentryRuntime_exactHeld_faithful (runtime : LivingRuntimeState reentryRuntimeProcess) :
    Unitary.conjStarAlgAut ℂ _ (star Producer.sourceJointUnitary) (reentryHeld runtime.tick.next.state.current) = reentryParentHeld := by
  rw [reentryRuntime_nextHeld]
  exact Producer.exactTarget_faithful

theorem reentryRuntime_independentOperator (runtime : LivingRuntimeState reentryRuntimeProcess) (O : Matrix Basis Basis ℂ) :
    (reentryHeld runtime.tick.next.state.current * O).trace = (reentryParentHeld * Producer.pullOperator O).trace := by
  rw [reentryRuntime_nextHeld]
  exact Producer.independent_operator_commutes O

theorem reentryRuntime_realization_account (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryResponse runtime.state.current).realized = reentryHeld runtime.tick.next.state.current +
      (reentryResponse runtime.state.current).inheritedResidual + (reentryResponse runtime.state.current).newNumericalResidual ∧
    ‖(reentryResponse runtime.state.current).totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 := by
  rw [reentryRuntime_response, reentryRuntime_nextHeld]
  exact ⟨Producer.total_error_reconstruction.2, Producer.total_realization_error_bound⟩

theorem reentryRuntime_retains_imaginary (runtime : LivingRuntimeState reentryRuntimeProcess) :
    ∃ i j, ((reentryResponse runtime.state.current).realized i j).im ≠ 0 := by
  rw [reentryRuntime_response]
  exact Producer.targetRealized_not_real_only

theorem reentryRuntime_energy_account (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryFrame runtime.tick.next.state.current).total - reentryParentFrame.total = Source.recordedEnergyChange ∧
    Source.engineEnergyChange = (reentryFrame runtime.tick.next.state.current).total - reentryParentFrame.total +
      Source.engineAccountingResidual := by
  rw [(reentryRuntime_actualBody runtime).2.1]
  exact ⟨Producer.nuclearRecordedEnergyChange, Producer.nuclearEngineVsPhysicalAccount⟩

theorem reentryRuntime_wholeResponse (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    (reentryCurrentLedger runtime.tick.next.state.current).rowResidualSum = -16 ∧
    (reentryCurrentPacket runtime.tick.next.state.current).targetGradientComponents.size = 6 ∧
    (∀ atom axis, Inertia.Producer.forceComponentSum
      (reentryCurrentPacket runtime.tick.next.state.current).targetGradientComponents atom axis +
      (reentryCurrentPacket runtime.tick.next.state.current).targetGradientRoundingResidual atom axis =
        (reentryCurrentPacket runtime.tick.next.state.current).targetGradientPicohartree atom axis) := by
  rw [(reentryRuntime_actualBody runtime).1, (reentryRuntime_actualBody runtime).2.2]
  exact ⟨Producer.nuclearTargetEnergyRows_exact, Producer.nuclearTargetEnergyResiduals.1,
    Producer.nuclearTarget_gradient_six, Producer.nuclearTargetGradientWholeLedger⟩

theorem reentryRuntime_elapsed_once :
    reentryPhysicalTime reentryRuntimeAfterFirst.state.current - reentryPhysicalTime reentryRuntimeSeed.state.current =
      Continuation.duration := by
  change reentryParentTime + Continuation.duration - reentryParentTime = _
  ring

theorem reentryRuntime_mechanical_energy (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentryFrame runtime.tick.next.state.current).total = Producer.targetMomentumKinetic +
      (reentryFrame runtime.tick.next.state.current).potential + Producer.targetKineticResidual ∧
    |Producer.targetKineticResidual| < (1 : ℚ) / 10 ^ 24 := by
  rw [(reentryRuntime_actualBody runtime).2.1]
  exact ⟨Producer.targetMechanicalEnergyWholeAccount, Producer.targetKineticResidual_bound⟩

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
