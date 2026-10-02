import H0mework.Versions.R2.Probability.EmpiricalRecovery.Model
import H0mework.Versions.R2.Fock.SourceHistory.ConditionalRecoveryRegression
import H0mework.Versions.R2.Fock.SourceHistory.ConditionalTransfer

/-! The original native update consumes sharp recovery error and the existing dynamic-model fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.Installed

open SourceConditionalTransfer SourceGeneratedRuntimeHistoryProbability SourceGeneratedEmpiricalHilbert
open SourceGeneratedScalarCofinalTopology.NativeProbability SourceOperationNative.Observed
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

variable {B : Type} [AddCommGroup B] (read : process.State → B)

theorem runtime_recovery_factorizes (depth : Nat) (value : Space read runtimeSeed depth)
    (decoder : Field (process := process) read → ℂ) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    sourceError read runtimeSeed depth value decoder = ‖residual read runtimeSeed depth value‖ ^ 2 +
      decoderError read runtimeSeed depth (transfer read runtimeSeed depth value) decoder ∧
      ‖residual read runtimeSeed depth value‖ ^ 2 ≤ sourceError read runtimeSeed depth value decoder ∧
      sourceError read runtimeSeed depth value (fun atom => transfer read runtimeSeed depth value atom) =
        ‖residual read runtimeSeed depth value‖ ^ 2 ∧
      (residual read runtimeSeed depth value = 0 ↔
        ∀ first second : Fin (depth + 1),
          modelPoint (process := process) read ((history runtimeSeed depth).stageAt first).next =
            modelPoint (process := process) read ((history runtimeSeed depth).stageAt second).next →
          value (fieldSample read runtimeSeed depth first) = value (fieldSample read runtimeSeed depth second)) ∧
      (∀ query index : Fin (depth + 1),
        index ∈ (conditionalIndices read runtimeSeed depth (nextAtom read runtimeSeed depth query)
            (nextAtom_supported read runtimeSeed depth query)).support ↔
          modelPoint (process := process) read ((history runtimeSeed depth).stageAt index).next =
            modelPoint (process := process) read ((history runtimeSeed depth).stageAt query).next) ∧
      (∀ index : Fin (depth + 1),
        let actor := (history runtimeSeed depth).stageAt index
        SourceGeneratedActionObservationHistory.modelAction (SourceOperationNative.sourceAction process)
            (SourceOperationNative.observer process read) (modelPoint (process := process) read (runtimeAt index.val)) =
          modelPoint (process := process) read actor.next ∧
          actor.next.current.visit.current = (runtimePayload index.val).nativeWrite.target ∧
          (process.toAnswerNextCausalWorld.emitted (ULift.up (sample runtimeSeed depth index)) =
              ULift.up actor.activated.generated ∧
            actor.activated.generated.occurrence =
              (runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
                (runtimeAt index.val).current.visit.current ∧
            HEq actor.wholeLedgerWriteBack
              ((runtimeAt index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
                (runtimeAt index.val).current.visit.current) ∧
            actor.next.current = actor.activated.nextCurrent)) ∧
      reconstruct read runtimeSeed depth (retainedUpdate read runtimeSeed depth value) = value ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, runtimePayload depth⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) ∧
      stage.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  rcases SourceConditionalTransfer.Installed.runtime_transfer_factorizes read depth value with
    ⟨_nextQuery, _transferRead, actors, reconstructed, _energy, sourceOccurrence, face, installation, stageFacts, next⟩
  refine ⟨error_decomposition read runtimeSeed depth value decoder,
    residual_lower_bound read runtimeSeed depth value decoder, transfer_attains read runtimeSeed depth value,
    zero_residual_iff_model read runtimeSeed depth value, conditional_model_fibre read runtimeSeed depth,
    ?_, reconstructed, sourceOccurrence, face, installation, stageFacts, next⟩
  intro index
  exact ⟨modelAction_point (process := process) read (runtimeAt index.val),
    (actors index).2.2.1, (actors index).2.2.2⟩

open SourceGeneratedEmpiricalHilbert.Controls

theorem pulse_information_disposition (decoder : Field (process := process) pulse → ℂ) :
    let runtime := runtimeAt 1
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    sourceError pulse runtimeSeed 1 indicatorValue decoder = (1 / 4 : ℝ) +
      decoderError pulse runtimeSeed 1 (transfer pulse runtimeSeed 1 indicatorValue) decoder ∧
      (1 / 4 : ℝ) ≤ sourceError pulse runtimeSeed 1 indicatorValue decoder ∧
      sourceError pulse runtimeSeed 1 indicatorValue (fun atom => transfer pulse runtimeSeed 1 indicatorValue atom) =
        (1 / 4 : ℝ) ∧
      modelPoint (process := process) pulse (runtimeAt 0) ≠ modelPoint (process := process) pulse (runtimeAt 1) ∧
      modelPoint (process := process) pulse (runtimeAt 0).tick.next =
        modelPoint (process := process) pulse (runtimeAt 1).tick.next ∧
      reconstruct pulse runtimeSeed 1 (retainedUpdate pulse runtimeSeed 1 indicatorValue) = indicatorValue ∧
      (runtimePayload 1).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive 1, runtimePayload 1⟩ ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = (runtimePayload 1).nativeWrite.target := by
  rcases runtime_recovery_factorizes pulse 1 indicatorValue decoder with
    ⟨error, lower, attained, _modelFibre, _conditionalFibre, _actors, reconstructed,
      sourceOccurrence, face, _installation, stageFacts, next⟩
  exact ⟨error.trans (congrArg (fun energy : ℝ => energy +
      decoderError pulse runtimeSeed 1 (transfer pulse runtimeSeed 1 indicatorValue) decoder) Pulse.residual_energy),
    Pulse.residual_energy.symm.trans_le lower, attained.trans Pulse.residual_energy,
    Pulse.current_models_distinct, Pulse.next_models_equal,
    reconstructed, sourceOccurrence, face, stageFacts.2.2.1, stageFacts.2.2.2, next⟩

end
end SourceConditionalRecovery.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
