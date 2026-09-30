import H0mework.Fock.HistoryCopy.InformationSource
import H0mework.Fock.PrimeField.InformationInventory
import H0mework.Fock.PrimeField.RecoveryConsumer

/-! The original active particle-wave face fixes the prime query's complete native calculation history. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCalculation

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery

noncomputable section

def frontier (bound : Nat) : SourceNativeRuntimeCalculationFrontierAt runtimeFacade runtimeSeed .particleWave :=
  .ofActive (runtimeActive 0) rfl (completionDepth sourceOwner bound)
    (fun stage sourcePayload material =>
      let current : CanonicalUnitArithmeticRoot.Current := (runtimeAt stage.val).current.visit.current
      HEq (SourceFactorizationAction.Fock.receipt sourcePayload) sourcePayload.operationDerivation ∧
        type_of% (SourceFactorizationAction.Fock.counts_next current) ∧
        sourceFieldAt material.next.current.visit.current =
          sourceFieldAt current + SourceFactorizationAction.Fock.birth current ∧
        SourceGeneratedConditionalInventory.snapshotCost material.next.state =
          SourceGeneratedConditionalInventory.snapshotCost stage.val +
            (if Nat.Prime (2 * stage.val + 5) then 0 else 1) ∧
        ∀ actor : Fin (SourceOwnedObservationHistory.NativeWindow.bound current + 1),
          SourceCopyInventory.inventoryCost (SourceOwnedObservationHistory.NativeWindow.point current actor) material.next.state =
            SourceCopyInventory.inventoryCost (SourceOwnedObservationHistory.NativeWindow.point current actor) stage.val +
              SourceCopyInventory.increment (SourceOwnedObservationHistory.NativeWindow.point current actor) stage.val)

theorem source_payload_is_original (bound : Nat) : (frontier bound).sourcePayload = runtimePayload 0 := rfl

theorem realization (bound : Nat) : SourceNativeRuntimeCalculationRealizationAt (frontier bound) where
  operationAt stage := ⟨SourceFactorizationAction.Fock.receipt_is_original (runtimePayload 0),
    (SourceFactorizationAction.Fock.runtime_source_factorization stage.val).1,
    (SourceFactorizationAction.Fock.runtime_source_factorization stage.val).2.1,
    by
      change SourceGeneratedConditionalInventory.snapshotCost (runtimeAt (stage.val + 1)).state = _
      rw [runtimeAt_state]
      exact SourceGeneratedConditionalInventory.actual_cost_step stage.val,
    by
      intro actor
      change SourceCopyInventory.inventoryCost _ (runtimeAt (stage.val + 1)).state = _
      rw [runtimeAt_state]
      exact SourceCopyInventory.cost_step _ stage.val⟩

def normal (bound : Nat) : SourceGeneratedRuntimeCalculationNormalFormAt (realization bound) := .generate (realization bound)

theorem target_is_original (bound : Nat) :
    (normal bound).targetRuntime = runtimeAt (completionDepth sourceOwner bound + 1) := rfl

end
end SourcePrimeCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
