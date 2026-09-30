import H0mework.Chemistry.LAlanineJointNext.RuntimeRuntimeReadouts

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem jointRuntime_nuclearCertificate : Producer.nuclearClosure := jointRuntime_sourceCertificate.2.1

theorem jointRuntime_actualBody (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointCurrentPacket runtime.tick.next.state.current = Source.stepReadout.nuclear ∧
    jointFrame runtime.tick.next.state.current = Source.stepReadout.nuclear.target ∧
    jointCurrentLedger runtime.tick.next.state.current = Source.stepReadout.nuclear.targetLedger := by
  change (jointResponse runtime.state.current).nuclear = _ ∧ (jointResponse runtime.state.current).nuclear.target = _ ∧
    (jointResponse runtime.state.current).nuclear.targetLedger = _
  rw [jointRuntime_response]
  exact ⟨rfl, rfl, rfl⟩

theorem jointRuntime_actualPhase (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointFrame runtime.tick.next.state.current).phase =
      Inertia.Mechanics.addResidual Producer.nuclearReference Producer.nuclearResidual := by
  rw [(jointRuntime_actualBody runtime).2.1]
  exact Producer.nuclearPhase_reconstruction

theorem jointRuntime_actualMovement (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointFrame runtime.tick.next.state.current).position ≠ jointParentFrame.position ∧
    (jointFrame runtime.tick.next.state.current).momentum ≠ jointParentFrame.momentum := by
  rw [(jointRuntime_actualBody runtime).2.1]
  exact ⟨Producer.nuclearPosition_changed, Producer.nuclearMomentum_changed⟩

theorem jointRuntime_exactHeld_faithful (runtime : LivingRuntimeState jointRuntimeProcess) :
    Unitary.conjStarAlgAut ℂ _ (star Producer.sourceJointUnitary) (jointHeld runtime.tick.next.state.current) = jointParentHeld := by
  rw [jointRuntime_nextHeld]
  exact Producer.exactTarget_faithful

theorem jointRuntime_independentOperator (runtime : LivingRuntimeState jointRuntimeProcess) (O : Matrix Basis Basis ℂ) :
    (jointHeld runtime.tick.next.state.current * O).trace = (jointParentHeld * Producer.pullOperator O).trace := by
  rw [jointRuntime_nextHeld]
  exact Producer.independent_operator_commutes O

theorem jointRuntime_realization_account (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointResponse runtime.state.current).realized = jointHeld runtime.tick.next.state.current +
      (jointResponse runtime.state.current).inheritedResidual + (jointResponse runtime.state.current).newNumericalResidual ∧
    ‖(jointResponse runtime.state.current).totalRealizationResidual‖ < (1 : ℝ) / 10 ^ 8 := by
  rw [jointRuntime_response, jointRuntime_nextHeld]
  exact ⟨Producer.total_error_reconstruction.2, Producer.total_realization_error_bound⟩

theorem jointRuntime_retains_imaginary (runtime : LivingRuntimeState jointRuntimeProcess) :
    ∃ i j, ((jointResponse runtime.state.current).realized i j).im ≠ 0 := by
  rw [jointRuntime_response]
  exact Producer.targetRealized_not_real_only

theorem jointRuntime_energy_account (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointFrame runtime.tick.next.state.current).total - jointParentFrame.total = Source.recordedEnergyChange ∧
    Source.engineEnergyChange = (jointFrame runtime.tick.next.state.current).total - jointParentFrame.total +
      Source.engineAccountingResidual := by
  rw [(jointRuntime_actualBody runtime).2.1]
  exact ⟨Producer.nuclearRecordedEnergyChange, Producer.nuclearEngineVsPhysicalAccount⟩

theorem jointRuntime_wholeResponse (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointCurrentLedger runtime.tick.next.state.current).rowToIntegralExact ∧
    (jointCurrentLedger runtime.tick.next.state.current).rowResidualSum = -12 ∧
    (jointCurrentPacket runtime.tick.next.state.current).targetGradientComponents.size = 6 ∧
    (∀ atom axis, Inertia.Producer.forceComponentSum
      (jointCurrentPacket runtime.tick.next.state.current).targetGradientComponents atom axis +
      (jointCurrentPacket runtime.tick.next.state.current).targetGradientRoundingResidual atom axis =
        (jointCurrentPacket runtime.tick.next.state.current).targetGradientPicohartree atom axis) := by
  rw [(jointRuntime_actualBody runtime).1, (jointRuntime_actualBody runtime).2.2]
  exact ⟨Producer.nuclearTargetEnergyRows_exact, Producer.nuclearTargetEnergyResiduals.1,
    Producer.nuclearTarget_gradient_six, Producer.nuclearTargetGradientWholeLedger⟩

theorem jointRuntime_elapsed_once :
    jointPhysicalTime jointRuntimeAfterFirst.state.current - jointPhysicalTime jointRuntimeSeed.state.current = Interface.duration :=
  Interface.one_elapsed_clock.1

theorem jointRuntime_mechanical_energy (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointFrame runtime.tick.next.state.current).total = Producer.targetMomentumKinetic +
      (jointFrame runtime.tick.next.state.current).potential + Producer.targetKineticResidual ∧
    |Producer.targetKineticResidual| < (1 : ℚ) / 10 ^ 24 := by
  rw [(jointRuntime_actualBody runtime).2.1]
  exact ⟨Producer.targetMechanicalEnergyWholeAccount, Producer.targetKineticResidual_bound⟩

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
