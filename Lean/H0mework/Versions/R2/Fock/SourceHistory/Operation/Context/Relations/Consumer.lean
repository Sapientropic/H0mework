import H0mework.Versions.R2.Realization.Operations.Context.Action
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Context.Consumer
import H0mework.Versions.R2.Fock.Cofinal.LogicEvidence

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePhysicalContextRelationConsumer

open SourceOperationEffects SourceOperationNative SourceOperationDerivations
open SourceOperationInventoryLift SourceOperationScalarPresentation
open SourceOperationScalarRelations
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationPrefix
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDerivation

noncomputable section

def readPaired (state : process.State) : Env (PairValue OperationValue) OperationVar :=
  pairEnvironment (SourcePhysicalContextConsumer.readEnv state)
    (SourcePhysicalContextConsumer.readEnv (process.successor state) -
      SourcePhysicalContextConsumer.readEnv state)

theorem readPaired_actual (runtime : LivingRuntimeState process) :
    readPaired runtime.state = stageEnvironment (SourceGeneratedRuntimeMaterialStageAt.generate runtime) := by
  unfold readPaired SourcePhysicalContextConsumer.readEnv stageEnvironment oldEnvironment incrementEnvironment
  rw [← map_sub]
  rfl

def sourceTree (runtime : LivingRuntimeState process) :
    Derivation (readPaired runtime.state) (liftExpr fockOperation)
      (.const ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace)) := by
  rw [readPaired_actual]
  exact stageDerivation (SourceGeneratedRuntimeMaterialStageAt.generate runtime)

def nextTree (runtime : LivingRuntimeState process) :
    Derivation (Context.environment (point runtime))
      ((Context.embed readPaired (liftExpr fockOperation)).subst Context.binding)
      (.const ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace)) :=
  Context.nextDerivation readPaired runtime (sourceTree runtime.tick.next)

def sourceReceipt (runtime : LivingRuntimeState process) :
    RelationIndex ℤ (readPaired runtime.state) OperationSort.parent →₀ ℤ :=
  Finsupp.single (.inl ⟨liftExpr fockOperation,
    .const ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace), sourceTree runtime⟩) 1

def nextReceipt (runtime : LivingRuntimeState process) :=
  Context.nextRelationWords readPaired runtime (sourceReceipt runtime.tick.next)

theorem receipt_boundary (runtime : LivingRuntimeState process) :
    relationMap (R := ℤ) (Context.environment (point runtime)) (nextReceipt runtime) =
      SourceOperationScalarRelations.substitution (R := ℤ) Context.binding
        (Context.words readPaired
          (relationMap (R := ℤ) (readPaired runtime.tick.next.state) (sourceReceipt runtime.tick.next))) :=
  LinearMap.congr_fun (Context.next_boundary_square readPaired runtime) (sourceReceipt runtime.tick.next)

theorem runtime_tree_receipt_inverse_ledger_next (depth : Nat) (alternative : ParentCarrier) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    let seen := ((Context.embed readPaired (liftExpr fockOperation)).subst Context.binding).eval
      (Context.environment (point runtime))
    seen = ((payloadAt runtime.tick.next).sourceState, (payloadAt runtime.tick.next).forcedTrace) ∧
    (jointMeasurement alternative = jointMeasurement (payloadAt runtime.tick.next).targetState ↔
      alternative - (seen.1 + seen.2) ∈ JointMeasurementKernel) ∧
    relationMap (R := ℤ) (Context.environment (point runtime)) (nextReceipt runtime) =
      SourceOperationScalarRelations.substitution (R := ℤ) Context.binding
        (Context.words readPaired
          (relationMap (R := ℤ) (readPaired runtime.tick.next.state) (sourceReceipt runtime.tick.next))) ∧
    runtimeFacade.readoutAt runtime .particleWave = .inl ⟨activeAt runtime, payloadAt runtime⟩ ∧
    stage.activated.generated.occurrence =
      runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
    HEq stage.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    stage.next.current = stage.activated.nextCurrent := by
  dsimp only
  have tree := (nextTree (runtimeAt depth)).sound
  simp only [Expr.eval] at tree
  obtain ⟨_, readout, occurrence, _installed, ledger, sameNext⟩ :=
    stage_source_factorizes (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth))
  refine ⟨tree, ?_, receipt_boundary _, readout, occurrence, ledger, sameNext⟩
  rw [tree]
  rw [← NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationCochain.stage_state_from_boundary
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth).tick.next)]
  exact (payloadAt (runtimeAt depth).tick.next).inverseFibreLaw alternative

end
end SourcePhysicalContextRelationConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
