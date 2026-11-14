import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Relations.Complex
import H0mework.Versions.Rc19e94a5.Arithmetic.FockDynamics.RootRuntime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNativeRelationWitnessConsumer

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceOperationNative SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation

noncomputable section

abbrev Word := Formal ℤ (Relations.PairedValue (process := process)) (Field.Var process) PUnit.unit

theorem runtime_generated_relation_witness_ledger_next (depth : Nat) (word : Word) :
    let runtime := runtimeAt depth
    let payload := runtimePayload depth
    let sourceEnvironment := Relations.pairedEnvironment runtime.tick.next
    let currentEnvironment := Relations.pairedEnvironment runtime
    let certificate := normalizationCertificate (R := ℤ) sourceEnvironment word
    let migrated := Relations.relationWords runtime certificate
    let syntaxAction := substitution (R := ℤ) (s := PUnit.unit) Relations.pairedBinding
    relationMap (R := ℤ) currentEnvironment migrated =
      syntaxAction (word - constantMap (R := ℤ) (valueMap (R := ℤ) sourceEnvironment word)) ∧
    (Relations.complexMorphism runtime).τ₁.hom certificate = migrated ∧
    (Relations.complexMorphism runtime).τ₂.hom = syntaxAction ∧
    (Relations.complexMorphism runtime).τ₃.hom = LinearMap.id ∧
    SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment
      (Relations.pairedBinding (process := process)) currentEnvironment = sourceEnvironment ∧
    ((payload.nativeRuntimeAction : Carrier process →ₗ[ℤ] Carrier process) = sourceAction process) ∧
    payload.nativeWrite = runtime.emittedOccurrence.2.write ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨runtimeActive depth, payload⟩ ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = runtimeFacade.process.stateAt
      (runtimeFacade.process.successor runtime.state) := by
  dsimp only
  have square := LinearMap.congr_fun (Relations.boundary_square (runtimeAt depth))
    (normalizationCertificate (R := ℤ) (Relations.pairedEnvironment (runtimeAt depth).tick.next) word)
  have reduced := source_reduction (R := ℤ) (Relations.pairedEnvironment (runtimeAt depth).tick.next) word
  obtain ⟨_, _, ledger, _, next⟩ := coversAt_factorizes (runtimeAt depth) .particleWave
  refine ⟨square.trans (congrArg (substitution (R := ℤ) (s := PUnit.unit) Relations.pairedBinding) reduced),
    rfl, rfl, rfl, Relations.actual_environment (runtimeAt depth),
    (runtimePayload depth).nativeRuntimeAction_eq, (runtimePayload depth).nativeWrite_source,
    runtimeReadout_is_particleWave depth, ledger, next⟩

end
end SourceNativeRelationWitnessConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
