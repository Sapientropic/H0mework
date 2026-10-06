import H0mework.Versions.AB.Chemistry.LAlanineReentry.RuntimeRuntimeInheritance
import H0mework.Versions.AB.Chemistry.LAlanineReentry.RegressionNuclear
import H0mework.Versions.AB.Chemistry.LAlanineReentry.RegressionSourcePhaseConsumer

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root
noncomputable section

theorem reentryRuntime_native_once :
    (reentrySource.toRootSource.actual.compile (reentryEmitted reentryRuntimeSeed.state.current)).kind = .nativeWrite := rfl

theorem reentryRuntime_readonly_mode (runtime : LivingRuntimeState reentryRuntimeProcess) :
    (reentrySource.toRootSource.actual.compile (reentryEmitted runtime.tick.next.state.current)).kind = .continuedTransport := rfl

theorem reentryRuntime_no_secondMD (runtime : LivingRuntimeState reentryRuntimeProcess) :
    reentryFrame runtime.tick.next.tick.next.state.current = reentryFrame runtime.tick.next.state.current ∧
    reentryHeld runtime.tick.next.tick.next.state.current = reentryHeld runtime.tick.next.state.current ∧
    reentryPhysicalTime runtime.tick.next.tick.next.state.current = reentryPhysicalTime runtime.tick.next.state.current ∧
    IsEmpty (ReentryV.NativeWriteAt runtime.tick.next.state.current) :=
  ⟨rfl, rfl, rfl, (reentryRuntime_next_readonly runtime).2⟩

theorem reentryRuntime_erasedImaginary_unreachable :
    ¬∃ runtime : LivingRuntimeState reentryRuntimeProcess, ∀ i j, ((reentryResponse runtime.state.current).realized i j).im = 0 := by
  rintro ⟨runtime, erased⟩
  rcases reentryRuntime_retains_imaginary runtime with ⟨i, j, retained⟩
  exact retained (erased i j)

theorem reentryRuntime_fourClock_unreachable :
    ¬∃ runtime : LivingRuntimeState reentryRuntimeProcess,
      reentryPhysicalTime runtime.tick.next.state.current = 4 * Propagation.Producer.nativeClockStep := by
  rintro ⟨runtime, advanced⟩
  rw [reentryRuntime_nextClock] at advanced
  have positive := Propagation.Producer.nativeClockStep_positive
  linarith

theorem reentryRuntime_oldSeed_not_reentered :
    reentryFrame reentryRuntimeSeed.state.current ≠ JointNext.Source.stepReadout.nuclear.current :=
  NuclearRegression.current_not_previous_ingress

theorem reentryRuntime_engineResidual_not_droppable (runtime : LivingRuntimeState reentryRuntimeProcess) :
    Source.engineEnergyChange ≠ (reentryFrame runtime.tick.next.state.current).total - reentryParentFrame.total := by
  rw [(reentryRuntime_energy_account runtime).1]
  exact Producer.nuclearEngine_not_recorded_change

theorem reentryRuntime_parent_preserved :
    reentryParentVisit = JointNext.Runtime.generatedJointAction.target.targetVisit ∧
    type_of% generatedReentryAction_receipt.receivedInstalledFaces ∧
    type_of% generatedReentryAction_receipt.receivedHistoricalFaces ∧
    type_of% generatedReentryAction_receipt.receivedFirstJointTrace ∧
    type_of% generatedReentryAction_receipt.sameCurrent :=
  ⟨reentryParent_generatedVisit, generatedReentryAction_receipt.receivedInstalledFaces,
    generatedReentryAction_receipt.receivedHistoricalFaces, generatedReentryAction_receipt.receivedFirstJointTrace,
    generatedReentryAction_receipt.sameCurrent⟩

theorem reentryRuntime_sourceGeneratedReentry :
    type_of% reentryRuntime_sourceCertificate ∧ type_of% reentryRuntime_nuclearCertificate ∧
    type_of% generatedReentryAction_next ∧ type_of% generatedReentryAction_answer ∧
    type_of% reentryRuntimeFirst_generated ∧ type_of% reentryRuntime_parent_preserved ∧
    type_of% reentryRuntime_seedClock ∧ type_of% reentryRuntime_elapsed_once ∧ type_of% reentryRuntime_native_once ∧
    type_of% reentryRuntime_erasedImaginary_unreachable ∧ type_of% reentryRuntime_fourClock_unreachable ∧
    type_of% reentryRuntime_oldSeed_not_reentered ∧
    (∀ runtime, type_of% (reentryRuntime_response runtime)) ∧
    (∀ runtime result ready, type_of% (reentryRuntime_ready_exact runtime result ready)) ∧
    (∀ runtime, type_of% (reentryRuntime_nextHeld runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_nextClock runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_readonly_mode runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_no_secondMD runtime)) ∧
    (∀ runtime projection, type_of% (reentryRuntimeFace_factorizes runtime projection)) ∧
    (∀ runtime, type_of% (reentryRuntime_nextReentry_inactive runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_readiness_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_physical_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_history_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_generator_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_realization_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_gradient_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_residual_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_actualBody runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_actualPhase runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_actualMovement runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_exactHeld_faithful runtime)) ∧
    (∀ runtime O, type_of% (reentryRuntime_independentOperator runtime O)) ∧
    (∀ runtime, type_of% (reentryRuntime_realization_account runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_parent_history runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_entire_error_inherited runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_inherits_both_parent_errors runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_energy_account runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_mechanical_energy runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_wholeResponse runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_engineResidual_not_droppable runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_wholeLedger_installed runtime)) ∧
    (∀ runtime, type_of% (reentryRuntime_row_identity runtime)) ∧
    type_of% PhaseConsumer.actual_phase_derivative ∧
    type_of% PhaseConsumer.actual_signal ∧
    type_of% PhaseConsumer.actual_phaseSignal_not_factor_through_realPart :=
  ⟨reentryRuntime_sourceCertificate, reentryRuntime_nuclearCertificate, generatedReentryAction_next, generatedReentryAction_answer,
    reentryRuntimeFirst_generated, reentryRuntime_parent_preserved, reentryRuntime_seedClock, reentryRuntime_elapsed_once,
    reentryRuntime_native_once, reentryRuntime_erasedImaginary_unreachable, reentryRuntime_fourClock_unreachable,
    reentryRuntime_oldSeed_not_reentered, reentryRuntime_response, reentryRuntime_ready_exact, reentryRuntime_nextHeld,
    reentryRuntime_nextClock, reentryRuntime_readonly_mode, reentryRuntime_no_secondMD, reentryRuntimeFace_factorizes,
    reentryRuntime_nextReentry_inactive, reentryRuntime_readiness_installed, reentryRuntime_physical_installed,
    reentryRuntime_history_installed, reentryRuntime_generator_installed, reentryRuntime_realization_installed,
    reentryRuntime_gradient_installed, reentryRuntime_residual_installed, reentryRuntime_actualBody, reentryRuntime_actualPhase,
    reentryRuntime_actualMovement, reentryRuntime_exactHeld_faithful, reentryRuntime_independentOperator,
    reentryRuntime_realization_account, reentryRuntime_parent_history, reentryRuntime_entire_error_inherited,
    reentryRuntime_inherits_both_parent_errors, reentryRuntime_energy_account, reentryRuntime_mechanical_energy,
    reentryRuntime_wholeResponse, reentryRuntime_engineResidual_not_droppable, reentryRuntime_wholeLedger_installed,
    reentryRuntime_row_identity, PhaseConsumer.actual_phase_derivative,
    PhaseConsumer.actual_signal, PhaseConsumer.actual_phaseSignal_not_factor_through_realPart⟩

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
