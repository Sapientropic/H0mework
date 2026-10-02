import H0mework.Realization.Operations.Action
import H0mework.Versions.R2.Fock.PrimeField.Action.Equation

/-! The original installed particle--wave face consumes the action on its
complete source words. A single prime observation retains its lost successor
coefficient in the current/next joint fibre, with the same receipt and tick. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeObservationAction

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery SourcePrimeCompletion SourcePrimeActionEquation
open SourceGeneratedObservationAction SourceGeneratedScalarDifferentialResidual

noncomputable section

theorem installed_action_is_original (depth : Nat) :
    (runtimePayload depth).nativeRuntimeAction = nativeAction :=
  (runtimePayload depth).nativeRuntimeAction_eq

theorem joint_fibre_retains_increment (prime : Nat.Primes) (stage : Nat)
    (left right : SourceOperationNative.Carrier process) :
    canonicalResidual (jointObservation nativeAction (sourceRow prime stage)) left =
      canonicalResidual (jointObservation nativeAction (sourceRow prime stage)) right ↔
    sourceRow prime stage left = sourceRow prime stage right ∧
      (if cut prime ≤ stage then 0 else left (cut prime - stage - 1)) =
      (if cut prime ≤ stage then 0 else right (cut prime - stage - 1)) := by
  rw [joint_fibre_iff, source_action_equation, source_action_equation]
  constructor
  · rintro ⟨same, next⟩
    rw [same] at next
    exact ⟨same, add_left_cancel next⟩
  · rintro ⟨same, increment⟩
    exact ⟨same, congrArg₂ (· + ·) same increment⟩

theorem action_defect_visible (prime : Nat.Primes) (stage : Nat)
    (outside : stage < cut prime) :
    actionDefect nativeAction (sourceRow prime stage)
      ⟨invisibleWord prime stage, invisible_word_current prime stage outside⟩ ≠ 0 := by
  rw [ne_eq, actionDefect_value_zero_iff, invisible_word_next prime stage outside]
  exact one_ne_zero

theorem no_current_coimage_action (prime : Nat.Primes) (stage : Nat)
    (outside : stage < cut prime) :
    ¬ ∃ next : ResidualCarrier (sourceRow prime stage) →ₗ[ℤ]
        ResidualCarrier (sourceRow prime stage),
      next.comp (canonicalResidual (sourceRow prime stage)) =
        (canonicalResidual (sourceRow prime stage)).comp nativeAction := by
  apply no_action_of_visible_fibre nativeAction (sourceRow prime stage)
    ⟨invisibleWord prime stage, invisible_word_current prime stage outside⟩
  rw [invisible_word_next prime stage outside]
  exact one_ne_zero

theorem stable_action_generated_unique (prime : Nat.Primes) (stage : Nat)
    (inside : cut prime ≤ stage) :
    ∃! next : ResidualCarrier (sourceRow prime stage) →ₗ[ℤ]
        ResidualCarrier (sourceRow prime stage),
      next.comp (canonicalResidual (sourceRow prime stage)) =
        (canonicalResidual (sourceRow prime stage)).comp nativeAction := by
  refine ⟨coimageAction prime stage inside, ?_, ?_⟩
  · exact LinearMap.ext (coimage_action_source prime stage inside)
  · intro other square
    apply LinearMap.ext
    intro quotient
    obtain ⟨word, rfl⟩ := Submodule.mkQ_surjective (LinearMap.ker (sourceRow prime stage)) quotient
    exact LinearMap.congr_fun square word

theorem runtime_action_joint_fibre_ledger_next (depth : Nat) (prime : Nat.Primes) :
    let runtime := runtimeAt depth
    let payload := runtimePayload depth
    let word := SourceOperationNative.point runtime
    let read := sourceRow prime 0
    let joint := canonicalResidual (jointObservation payload.nativeRuntimeAction read) word
    payload.nativeRuntimeAction word = SourceOperationNative.point runtime.tick.next ∧
    jointCurrent payload.nativeRuntimeAction read joint = canonicalResidual read word ∧
    jointNext payload.nativeRuntimeAction read joint =
      canonicalResidual read (SourceOperationNative.point runtime.tick.next) ∧
    read (SourceOperationNative.point runtime.tick.next) = read word +
      (if cut prime ≤ 0 then 0 else word (cut prime - 1)) ∧
    payload.nativeWrite = runtime.emittedOccurrence.2.write ∧
    payload.targetState = payload.sourceState + payload.forcedTrace ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, payload⟩ ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = runtimeFacade.process.stateAt
      (runtimeFacade.process.successor runtime.state) := by
  dsimp only
  have actionPoint : (runtimePayload depth).nativeRuntimeAction
      (SourceOperationNative.point (process := process) (runtimeAt depth)) =
      SourceOperationNative.point (process := process) (runtimeAt depth).tick.next := by
    rw [installed_action_is_original]
    exact SourceOperationNative.sourceAction_point (runtimeAt depth)
  obtain ⟨_, _, ledger, _, next⟩ := coversAt_factorizes (runtimeAt depth) .particleWave
  refine ⟨actionPoint, joint_current_source _ _ _, ?_, ?_,
    (runtimePayload depth).nativeWrite_source, (runtimePayload depth).stateUpdate,
    runtimeReadout_is_particleWave depth, ledger, next⟩
  · rw [installed_action_is_original]
    exact (joint_next_source nativeAction (sourceRow prime 0)
      (SourceOperationNative.point (runtimeAt depth))).trans
        (congrArg (canonicalResidual (sourceRow prime 0))
          (SourceOperationNative.sourceAction_point (runtimeAt depth)))
  · rw [← actionPoint, installed_action_is_original]
    exact source_action_equation prime 0 (SourceOperationNative.point (runtimeAt depth))

end
end SourcePrimeObservationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
