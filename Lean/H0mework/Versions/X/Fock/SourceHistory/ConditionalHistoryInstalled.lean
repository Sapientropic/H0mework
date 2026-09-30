import H0mework.Versions.X.Fock.SourceHistory.TerminalRecoveryRegression
import H0mework.Versions.X.Fock.SourceHistory.ConditionalRecovery

/-! Actual advanced history and its final source occurrence consume the full terminal recovery cost. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRecovery.History.Installed

open SourceGeneratedEmpiricalHilbert SourceGeneratedRuntimeHistoryProbability SourceConditionalTransfer
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

private theorem runtime_advance_add (first second : Nat) :
    (runtimeSeed.advance first).advance second = runtimeAt (first + second) := by
  induction second with
  | zero => rfl
  | succ second previous =>
      exact congrArg (fun runtime : LivingRuntimeState process => runtime.tick.next) previous

variable {B : Type} [AddCommGroup B] (read : process.State → B)

theorem terminal_is_actual_next (bound depth : Nat) :
    fieldSample read (runtimeSeed.advance (depth + 1)) bound (Fin.last bound) =
      fieldPoint read (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (depth + bound))).next.state := by
  have shifted := nextAtom_eq_next_sample read (runtimeSeed.advance depth) bound (Fin.last bound)
  apply shifted.symm.trans
  apply (fieldPoint_action read (sample (runtimeSeed.advance depth) bound (Fin.last bound))).trans
  exact congrArg (fun runtime : LivingRuntimeState process => fieldPoint read runtime.tick.next.state)
    (runtime_advance_add depth bound)

theorem runtime_terminal_factorizes (bound depth : Nat) (value : Space read runtimeSeed bound)
    (decoder : Field (process := process) read → ℂ) :
    let runtime := runtimeAt (depth + bound)
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    type_of% (terminalError_decomposition read runtimeSeed bound depth value decoder) ∧
      type_of% (terminalError_lower_bound read runtimeSeed bound depth value decoder) ∧
      type_of% (terminalError_attains read runtimeSeed bound depth value) ∧
      (∀ tick : Fin (depth + 1), type_of% (floor_increment_conditional read runtimeSeed bound tick.val value)) ∧
      (∀ tick : Fin (depth + 1), type_of% (no_increment_iff_model read runtimeSeed bound tick.val value)) ∧
      (∀ tick : Fin (depth + 1), ∀ index : Fin (bound + 1),
        type_of% (sample_factorizes (runtimeSeed.advance tick.val) bound index)) ∧
      (retainedHistory read runtimeSeed bound (depth + 1)).symm
        (retainedHistory read runtimeSeed bound (depth + 1) value) = value ∧
      fieldSample read (runtimeSeed.advance (depth + 1)) bound (Fin.last bound) = fieldPoint read stage.next.state ∧
      (runtimePayload (depth + bound)).sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive (depth + bound), runtimePayload (depth + bound)⟩ ∧
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
      stage.next.current.visit.current = (runtimePayload (depth + bound)).nativeWrite.target := by
  have installed := coversAt_factorizes (runtimeAt (depth + bound)) .particleWave
  exact ⟨terminalError_decomposition read runtimeSeed bound depth value decoder,
    terminalError_lower_bound read runtimeSeed bound depth value decoder,
    terminalError_attains read runtimeSeed bound depth value,
    fun tick => floor_increment_conditional read runtimeSeed bound tick.val value,
    fun tick => no_increment_iff_model read runtimeSeed bound tick.val value,
    fun tick index => sample_factorizes (runtimeSeed.advance tick.val) bound index,
    (retainedHistory read runtimeSeed bound (depth + 1)).symm_apply_apply value,
    terminal_is_actual_next read bound depth, (runtimePayload (depth + bound)).sourceOccurrence_eq,
    runtimeReadout_is_particleWave (depth + bound), installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt (depth + bound))).factorizes,
    runtime_current_next (depth + bound)⟩

end
end SourceConditionalRecovery.History.Installed
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
