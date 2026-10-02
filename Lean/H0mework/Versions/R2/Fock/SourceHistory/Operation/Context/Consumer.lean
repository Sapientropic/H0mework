import H0mework.Versions.R2.Realization.Operations.Context.Words
import H0mework.Versions.R2.Fock.Cofinal.OperationCochain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalContextConsumer

open SourceOperationEffects SourceOperationScalarRelations SourceOperationNative
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix

noncomputable section

def readEnv (state : process.State) : Env OperationValue OperationVar :=
  environmentProjection (sourceMaterial state)

def inventory (runtime : LivingRuntimeState process) :=
  updateInventory (R := ℤ) (s := Sum.inl OperationSort.parent)
    (Context.environment (PhysicalValue := OperationValue) (point runtime))
    (Context.environment (PhysicalValue := OperationValue) (point runtime.tick.next - point runtime))

theorem original_inventory (runtime : LivingRuntimeState process)
    (word : Formal ℤ OperationValue OperationVar OperationSort.parent) :
    updateInventory (R := ℤ) (readEnv runtime.state)
      (readEnv runtime.tick.next.state - readEnv runtime.state) word =
        stageInventory (SourceGeneratedRuntimeMaterialStageAt.generate runtime) word := by
  unfold readEnv
  rw [← map_sub]
  rfl

theorem current_pair (runtime : LivingRuntimeState process)
    (word : Formal ℤ OperationValue OperationVar OperationSort.parent) :
    inventory runtime (Context.words readEnv word) =
      stageInventory (SourceGeneratedRuntimeMaterialStageAt.generate runtime) word :=
  (LinearMap.congr_fun (Context.inventory_square readEnv runtime) word).trans
    (original_inventory runtime word)

theorem literalnext_pair (runtime : LivingRuntimeState process)
    (word : Formal ℤ OperationValue OperationVar OperationSort.parent) :
    inventory runtime ((substitution (R := ℤ) Context.binding) (Context.words readEnv word)) =
      stageInventory (SourceGeneratedRuntimeMaterialStageAt.generate runtime.tick.next) word :=
  (LinearMap.congr_fun (Context.next_inventory_square readEnv runtime) word).trans
    (original_inventory runtime.tick.next word)

theorem runtime_physical_equation_context_ledger_next (depth : Nat) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let current := inventory runtime (Context.words readEnv OperationRelations.operationWord)
    let next := inventory runtime ((substitution (R := ℤ) Context.binding)
      (Context.words readEnv OperationRelations.operationWord))
    current = ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) ∧
    next = ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) ∧
    (payloadAt runtime).targetState = current.1 + current.2 ∧
    (payloadAt runtime.tick.next).targetState = next.1 + next.2 ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨activeAt runtime, payloadAt runtime⟩ ∧
    stage.activated.generated.occurrence =
      runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
    HEq stage.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    stage.next.current = stage.activated.nextCurrent := by
  dsimp only
  have current := (current_pair (runtimeAt depth) OperationRelations.operationWord).trans
    (stage_reads_installed_payload (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)))
  have next := (literalnext_pair (runtimeAt depth) OperationRelations.operationWord).trans
    (stage_reads_installed_payload (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth).tick.next))
  obtain ⟨_, readout, occurrence, _installed, ledger, sameNext⟩ :=
    stage_source_factorizes (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth))
  refine ⟨current, next, ?_, ?_, readout, occurrence, ledger, sameNext⟩
  · rw [current]
    exact NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationCochain.stage_state_from_boundary
      (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth))
  · rw [next]
    exact NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationCochain.stage_state_from_boundary
      (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth).tick.next)

end
end SourcePhysicalContextConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
