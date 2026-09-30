import H0mework.Chemistry.LAlanineJointNext.RuntimeRuntimeConsumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

theorem jointRuntime_native_once :
    (jointSource.toRootSource.actual.compile (jointEmitted jointRuntimeSeed.state.current)).kind = .nativeWrite := rfl

theorem jointRuntime_readonly_mode (runtime : LivingRuntimeState jointRuntimeProcess) :
    (jointSource.toRootSource.actual.compile (jointEmitted runtime.tick.next.state.current)).kind = .continuedTransport := rfl

theorem jointRuntime_no_secondMD (runtime : LivingRuntimeState jointRuntimeProcess) :
    jointFrame runtime.tick.next.tick.next.state.current = jointFrame runtime.tick.next.state.current ∧
    jointHeld runtime.tick.next.tick.next.state.current = jointHeld runtime.tick.next.state.current ∧
    jointPhysicalTime runtime.tick.next.tick.next.state.current = jointPhysicalTime runtime.tick.next.state.current ∧
    IsEmpty (JointV.NativeWriteAt runtime.tick.next.state.current) :=
  ⟨rfl, rfl, rfl, (jointRuntime_next_readonly runtime).2⟩

theorem jointRuntime_erasedImaginary_unreachable :
    ¬∃ runtime : LivingRuntimeState jointRuntimeProcess, ∀ i j, ((jointResponse runtime.state.current).realized i j).im = 0 := by
  rintro ⟨runtime, erased⟩
  rcases jointRuntime_retains_imaginary runtime with ⟨i, j, retained⟩
  exact retained (erased i j)

theorem jointRuntime_threeClock_unreachable :
    ¬∃ runtime : LivingRuntimeState jointRuntimeProcess,
      jointPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  rintro ⟨runtime, advanced⟩
  rw [jointRuntime_nextClock] at advanced
  have positive := Propagation.Producer.nativeClockStep_positive
  linarith

theorem jointRuntime_engineResidual_not_droppable (runtime : LivingRuntimeState jointRuntimeProcess) :
    Source.engineEnergyChange ≠ (jointFrame runtime.tick.next.state.current).total - jointParentFrame.total := by
  rw [(jointRuntime_energy_account runtime).1]
  exact Producer.nuclearEngine_not_recorded_change

theorem jointRuntime_parent_preserved :
    jointParentVisit = HeldForce.Runtime.generatedHeldForceAction.target.targetVisit ∧
    type_of% generatedJointAction_receipt.receivedInstalledFaces ∧
    type_of% generatedJointAction_receipt.receivedFirstForceTrace ∧
    type_of% generatedJointAction_receipt.sameCurrent :=
  ⟨jointParent_generatedVisit, generatedJointAction_receipt.receivedInstalledFaces,
    generatedJointAction_receipt.receivedFirstForceTrace, generatedJointAction_receipt.sameCurrent⟩

theorem jointRuntime_sourceGeneratedJointStep :
    type_of% jointRuntime_sourceCertificate ∧ type_of% jointRuntime_nuclearCertificate ∧
    type_of% generatedJointAction_next ∧ type_of% generatedJointAction_answer ∧
    type_of% jointRuntimeFirst_generated ∧ type_of% jointRuntime_parent_preserved ∧
    type_of% jointRuntime_seedClock ∧ type_of% jointRuntime_elapsed_once ∧ type_of% jointRuntime_native_once ∧
    type_of% jointRuntime_erasedImaginary_unreachable ∧ type_of% jointRuntime_threeClock_unreachable ∧
    (∀ runtime, type_of% (jointRuntime_response runtime)) ∧
    (∀ runtime result ready, type_of% (jointRuntime_ready_exact runtime result ready)) ∧
    (∀ runtime, type_of% (jointRuntime_nextHeld runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_nextClock runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_readonly_mode runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_no_secondMD runtime)) ∧
    (∀ runtime projection, type_of% (jointRuntimeFace_factorizes runtime projection)) ∧
    (∀ runtime, type_of% (jointRuntime_nextJoint_inactive runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_readiness_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_physical_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_history_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_generator_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_realization_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_gradient_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_residual_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_actualBody runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_actualPhase runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_actualMovement runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_exactHeld_faithful runtime)) ∧
    (∀ runtime O, type_of% (jointRuntime_independentOperator runtime O)) ∧
    (∀ runtime, type_of% (jointRuntime_realization_account runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_energy_account runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_mechanical_energy runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_wholeResponse runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_engineResidual_not_droppable runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_wholeLedger_installed runtime)) ∧
    (∀ runtime, type_of% (jointRuntime_row_identity runtime)) :=
  ⟨jointRuntime_sourceCertificate, jointRuntime_nuclearCertificate, generatedJointAction_next, generatedJointAction_answer,
    jointRuntimeFirst_generated, jointRuntime_parent_preserved, jointRuntime_seedClock, jointRuntime_elapsed_once,
    jointRuntime_native_once, jointRuntime_erasedImaginary_unreachable, jointRuntime_threeClock_unreachable,
    jointRuntime_response, jointRuntime_ready_exact, jointRuntime_nextHeld, jointRuntime_nextClock,
    jointRuntime_readonly_mode, jointRuntime_no_secondMD, jointRuntimeFace_factorizes, jointRuntime_nextJoint_inactive,
    jointRuntime_readiness_installed, jointRuntime_physical_installed, jointRuntime_history_installed, jointRuntime_generator_installed,
    jointRuntime_realization_installed, jointRuntime_gradient_installed, jointRuntime_residual_installed,
    jointRuntime_actualBody, jointRuntime_actualPhase, jointRuntime_actualMovement, jointRuntime_exactHeld_faithful,
    jointRuntime_independentOperator, jointRuntime_realization_account, jointRuntime_energy_account, jointRuntime_mechanical_energy,
    jointRuntime_wholeResponse, jointRuntime_engineResidual_not_droppable, jointRuntime_wholeLedger_installed, jointRuntime_row_identity⟩

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
