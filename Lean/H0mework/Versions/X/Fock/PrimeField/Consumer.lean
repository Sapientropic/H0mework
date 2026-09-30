import H0mework.Versions.X.Fock.PrimeField.Receipt
import H0mework.Versions.X.Fock.SourceHistory.Installed

/-! The original measurement and full inverse fibre consume the source-born field effect at the same installed write. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction.Fock

open ArithmeticGeneration
open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open SourceOwnedObservationHistory.Installed

noncomputable section

theorem runtime_source_factorization (depth : Nat) :
    let runtime := runtimeAt depth
    let current : CanonicalUnitArithmeticRoot.Current := runtime.current.visit.current
    let payload := runtimePayload depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    type_of% (counts_next current) ∧
      sourceFieldAt stage.next.current.visit.current = sourceFieldAt current + birth current ∧
      HEq (relation payload) payload.operationRelation ∧
      HEq (receipt payload) payload.operationDerivation ∧
      payload.operationValues = [diagonalInclusion (birth current),
        pairInclusion (sourceFieldAt current ⊗ₜ[ℤ] birth current),
        pairInclusion (birth current ⊗ₜ[ℤ] sourceFieldAt current),
        pairInclusion (birth current ⊗ₜ[ℤ] birth current)] ∧
      payload.targetState = payload.sourceState + secondQuantizedEffect (sourceFieldAt current) (birth current) ∧
      jointMeasurement payload.targetState = jointMeasurement payload.sourceState +
        jointMeasurement (secondQuantizedEffect (sourceFieldAt current) (birth current)) ∧
      payload.targetFibre.val = payload.sourceState + secondQuantizedEffect (sourceFieldAt current) (birth current) ∧
      (∀ alternative : ParentCarrier,
        jointMeasurement alternative = jointMeasurement (payload.sourceState + secondQuantizedEffect (sourceFieldAt current) (birth current)) ↔
          alternative - (payload.sourceState + secondQuantizedEffect (sourceFieldAt current) (birth current)) ∈ JointMeasurementKernel) ∧
      (∀ prime : OwnerPrimeIndexAt (liveGlobalOwner current) (scanIndex current), ∀ power : CanonicalUnitArithmeticFactorizationOccurrence.ExponentIndex (history current) prime,
        type_of% ((ownerEvenFactorization (liveGlobalOwner current) (scanIndex current)).actualPrimePower_joint_landing prime power)) ∧
      (∀ prime : OwnerPrimeIndexAt (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current)) (scanIndex (CanonicalUnitArithmeticRoot.next current)),
        ∀ power : CanonicalUnitArithmeticFactorizationOccurrence.ExponentIndex (history (CanonicalUnitArithmeticRoot.next current)) prime,
        type_of% ((ownerEvenFactorization (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current))
          (scanIndex (CanonicalUnitArithmeticRoot.next current))).actualPrimePower_joint_landing prime power)) ∧
      (∀ index : Fin (SourceOwnedObservationHistory.NativeWindow.bound current + 1), type_of% (window_actor_factorizes depth index)) ∧
      type_of% payload.sourceOwnerOccurrence ∧ type_of% payload.targetOwnerOccurrence ∧
      payload.sourceOccurrence = runtime.emittedOccurrence ∧
      runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, payload⟩ ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      HEq stage.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      stage.next.current = stage.activated.nextCurrent ∧
      stage.next.current.visit.current = payload.nativeWrite.target := by
  let current : CanonicalUnitArithmeticRoot.Current := (runtimeAt depth).current.visit.current
  let payload := runtimePayload depth
  have actualField : sourceFieldAt (runtimeAt depth).tick.next.current.visit.current =
      sourceFieldAt current + birth current :=
    (congrArg sourceFieldAt ((runtime_current_next depth).trans payload.nativeWrite.target_eq)).trans (field_next current)
  have measured := congrArg jointMeasurement (state_from_source payload)
  rw [map_add] at measured
  have fibre := payload.inverseFibreLaw
  rw [state_from_source payload] at fibre
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  have stageFacts := (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes
  exact ⟨counts_next current, actualField, relation_is_original payload, receipt_is_original payload,
    (operation_values payload).trans (evaluateOperationTrace_exact _ _), state_from_source payload, measured,
    payload.targetFibre_eq.trans (state_from_source payload), fibre,
    (fun prime power => (ownerEvenFactorization (liveGlobalOwner current) (scanIndex current)).actualPrimePower_joint_landing prime power),
    (fun prime power => (ownerEvenFactorization (liveGlobalOwner (CanonicalUnitArithmeticRoot.next current))
      (scanIndex (CanonicalUnitArithmeticRoot.next current))).actualPrimePower_joint_landing prime power),
    window_actor_factorizes depth, payload.sourceOwnerOccurrence, payload.targetOwnerOccurrence,
    payload.sourceOccurrence_eq, runtimeReadout_is_particleWave depth, installed.2.2.2.1,
    stageFacts.2.2.1, stageFacts.2.2.2, runtime_current_next depth⟩

end
end SourceFactorizationAction.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
