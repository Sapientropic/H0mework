import H0mework.Versions.R2.Fock.Cofinal.DynamicsPrefix

/-! Retained source witnesses extend through the previous generated history target tick. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDynamics

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open SourceOperationLogic SourceGeneratedScalarDifferentialResidual

noncomputable section

def restrictPrefix (depth bound : Nat) : PrefixModel depth (bound + 1) →ₗ[ℤ] PrefixModel depth bound :=
  (prefixData depth).quotientTransition (prefix_compatible depth) bound

theorem restrictPrefix_source (depth bound : Nat) (word : FormalCarrier) :
    restrictPrefix depth bound (prefixSource depth (bound + 1) word) = prefixSource depth bound word :=
  LinearMap.congr_fun
    ((prefixData depth).quotientTransition_quotientMap (prefix_compatible depth) bound) word

/-- The retained source generates the next model point; the old projected point supplies no selector. -/
def extendWitness (depth bound : Nat) {point : PrefixModel depth bound}
    (source : Fibre (prefixEvaluator depth bound) point) :
    Σ nextPoint : PrefixModel depth (bound + 1),
      Fibre (prefixEvaluator depth (bound + 1)) nextPoint ×
        PLift (restrictPrefix depth bound nextPoint = point) :=
  ⟨prefixSource depth (bound + 1) source.val,
    sourceWitness (prefixEvaluator depth (bound + 1)) source.val,
    ⟨(restrictPrefix_source depth bound source.val).trans source.property⟩⟩

theorem extendWitness_keeps_source (depth bound : Nat) {point : PrefixModel depth bound}
    (source : Fibre (prefixEvaluator depth bound) point) :
    (extendWitness depth bound source).2.1.val = source.val := rfl

theorem append_is_previous_target_tick (depth bound : Nat) :
    ((materialHistory depth (bound + 1)).stageAt (Fin.last (bound + 1))).activated =
      (materialHistory depth bound).target.tick := rfl

theorem extended_actual_state (depth bound : Nat) :
    (residualEquivRange (lastEvaluator depth (bound + 1))
      (lastMap depth (bound + 1)
        (extendWitness depth bound
          (sourceWitness (prefixEvaluator depth bound) OperationRelations.operationWord)).1)).val =
      (payloadAt (materialHistory depth bound).target).targetState :=
  last_actual_read depth (bound + 1)

theorem extension_factorizes (depth bound : Nat) :
    let stage := (materialHistory depth (bound + 1)).stageAt (Fin.last (bound + 1))
    let runtime := (materialHistory depth bound).target
    stage.activated = runtime.tick ∧
    (residualEquivRange (lastEvaluator depth (bound + 1))
      (lastMap depth (bound + 1)
        (extendWitness depth bound
          (sourceWitness (prefixEvaluator depth bound) OperationRelations.operationWord)).1)).val =
      (payloadAt runtime).targetState ∧
    runtimeFacade.readoutAt runtime .particleWave =
      .inl ⟨activeAt runtime, payloadAt runtime⟩ ∧
    stage.activated.generated.occurrence =
      runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        runtime.current.visit.current ∧
    HEq (runtimeFacade.readoutAt runtime .particleWave)
      (stage.activated.generated.projectionOutcome
        ((runtimeFacade.installationAt runtime .particleWave).embed
          (runtimeFacade.projectionAt runtime .particleWave))) ∧
    HEq stage.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        runtime.current.visit.current) ∧
    stage.next.current = stage.activated.nextCurrent := by
  have source := whole_prefix_factorizes depth (bound + 1) (Fin.last (bound + 1))
  exact ⟨append_is_previous_target_tick depth bound, extended_actual_state depth bound, source.2⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDynamics
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
