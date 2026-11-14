import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalArithmeticState.ParticleWave.Fock.Runtime.SourceHistory.PrimeField.Action.FiniteModel
import H0mework.Versions.Rc19e94a5.Fock.PrimeField.Action.Consumer

/-! The finite sufficient prime window is read from the original generated
material history. Recovery and advance retain the original installed Fock
receipt, complete ledger and the actual next at every material stage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeActionSaturation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery SourcePrimeCompletion SourcePrimeObservationAction
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual

noncomputable section

theorem runtime_window_reads (prime : Nat.Primes) (depth : Nat)
    (index : Fin (cut prime + 1)) :
    (modelWindowValue prime (projection nativeAction (originalRead prime)
      (SourceOperationNative.point (runtimeAt depth)))).val index =
      primeRead prime (rawField ((runtimeAt depth).advance index.val).state) := by
  change originalRead prime ((nativeAction ^ index.val)
    (SourceOperationNative.point (runtimeAt depth))) = _
  rw [SourceOperationNative.Observed.sourceAction_pow_point]
  rw [originalRead, source_row_is_prime_read]
  change primeRead prime (observation (SourceOperationNative.point
    ((runtimeAt depth).advance index.val))) = _
  rw [SourceOperationNative.observer_point]

theorem runtime_window_advance (prime : Nat.Primes) (depth : Nat) :
    FiniteRecurrence.advance (cut prime) (coefficients prime)
      (modelWindowRead prime (projection nativeAction (originalRead prime)
        (SourceOperationNative.point (runtimeAt depth)))) =
    modelWindowRead prime (projection nativeAction (originalRead prime)
      (SourceOperationNative.point (runtimeAt depth).tick.next)) := by
  rw [modelWindowRead_source, modelWindowRead_source]
  have generated := LinearMap.congr_fun (finite_prefix_action prime)
    (SourceOperationNative.point (runtimeAt depth))
  change _ = prefixEvaluator nativeAction (originalRead prime) (cut prime)
    (nativeAction (SourceOperationNative.point (runtimeAt depth))) at generated
  rw [SourceOperationNative.sourceAction_point] at generated
  exact generated

theorem runtime_finite_model_material_ledger_next (prime : Nat.Primes) (depth : Nat) :
    let runtime := runtimeAt depth
    let history := SourceGeneratedRuntimeMaterialHistoryAt.generate runtime (cut prime + 1)
    let model := projection nativeAction (originalRead prime) (SourceOperationNative.point runtime)
    recoverWindow prime (modelWindowValue prime model) = model ∧
    (∀ index : Fin (cut prime + 1),
      (modelWindowValue prime model).val index = primeRead prime (rawField (runtime.advance index.val).state) ∧
      (history.stageAt index).next = (runtime.advance index.val).tick.next ∧
      HEq (history.stageAt index).wholeLedgerWriteBack
        ((runtime.advance index.val).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime.advance index.val).current.visit.current)) ∧
    FiniteRecurrence.advance (cut prime) (coefficients prime) (modelWindowRead prime model) =
      modelWindowRead prime (projection nativeAction (originalRead prime)
        (SourceOperationNative.point runtime.tick.next)) ∧
    (runtimePayload depth).nativeWrite = runtime.emittedOccurrence.2.write ∧
    (runtimePayload depth).targetState = (runtimePayload depth).sourceState + (runtimePayload depth).forcedTrace ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, runtimePayload depth⟩ ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = runtimeFacade.process.stateAt (runtimeFacade.process.successor runtime.state) ∧
    HEq history.target.tick.generated.wholeLedgerWriteBack
      (history.target.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt history.target.current.visit.current) ∧
    history.target.tick.nextCurrent = runtimeFacade.process.stateAt
      (runtimeFacade.process.successor history.target.state) := by
  dsimp only
  let history := SourceGeneratedRuntimeMaterialHistoryAt.generate (runtimeAt depth) (cut prime + 1)
  obtain ⟨_, _, ledger, _, next⟩ := coversAt_factorizes (runtimeAt depth) .particleWave
  have target := history.target_factorizes
  refine ⟨recoverWindow_modelWindowValue prime _, ?_, runtime_window_advance prime depth,
    (runtimePayload depth).nativeWrite_source, (runtimePayload depth).stateUpdate,
    runtimeReadout_is_particleWave depth, ledger, next, target.2.2.1, target.2.2.2⟩
  intro index
  exact ⟨runtime_window_reads prime depth index, rfl,
    (history.stageAt index).factorizes.2.2.1⟩

end
end SourcePrimeActionSaturation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
