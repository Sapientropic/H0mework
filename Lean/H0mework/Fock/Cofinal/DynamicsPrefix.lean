import H0mework.Realization.Logic.QuantifiedUpdate
import H0mework.Fock.Cofinal.LogicConsumers

/-! The complete original prefix supplies both endpoints and every intermediate actual stage. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDynamics

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open ParticleWaveFockOperationDerivation SourceOperationLogic SourceOperationDynamics
open SourceGeneratedScalarDifferentialResidual

noncomputable section

abbrev PrefixModel (depth bound : Nat) := Scope (prefixEvaluator depth bound)

def prefixSource (depth bound : Nat) (word : FormalCarrier) : PrefixModel depth bound :=
  q (prefixEvaluator depth bound) word

def firstRead (bound : Nat) : PrefixCarrier bound →ₗ[ℤ] ParentCarrier :=
  (LinearMap.fst ℤ ParentCarrier ParentCarrier).comp (LinearMap.proj 0)

def lastRead (bound : Nat) : PrefixCarrier bound →ₗ[ℤ] ParentCarrier :=
  (SourceOperationRelations.additionReadout (Value := OperationValue) (s := OperationSort.parent)).comp
    (LinearMap.proj (Fin.last bound))

def firstEvaluator (depth bound : Nat) := (firstRead bound).comp (prefixEvaluator depth bound)
def lastEvaluator (depth bound : Nat) := (lastRead bound).comp (prefixEvaluator depth bound)

def firstMap (depth bound : Nat) := projectScope (prefixEvaluator depth bound) (firstRead bound)
def lastMap (depth bound : Nat) := projectScope (prefixEvaluator depth bound) (lastRead bound)

theorem prefix_reads_every_stage (depth bound : Nat) (word : FormalCarrier)
    (index : Fin (bound + 1)) :
    (prefixData depth).stageRealization bound (prefixSource depth bound word) index =
      stageInventory ((materialHistory depth bound).stageAt index) word := rfl

theorem first_read_source (depth bound : Nat) (word : FormalCarrier) :
    (residualEquivRange (firstEvaluator depth bound)
      (firstMap depth bound (prefixSource depth bound word))).val =
        (stageInventory ((materialHistory depth bound).stageAt 0) word).1 := rfl

theorem last_read_source (depth bound : Nat) (word : FormalCarrier) :
    (residualEquivRange (lastEvaluator depth bound)
      (lastMap depth bound (prefixSource depth bound word))).val =
        (stageInventory ((materialHistory depth bound).stageAt (Fin.last bound)) word).1 +
        (stageInventory ((materialHistory depth bound).stageAt (Fin.last bound)) word).2 := rfl

theorem first_actual_read (depth bound : Nat) :
    (residualEquivRange (firstEvaluator depth bound)
      (firstMap depth bound (prefixSource depth bound OperationRelations.operationWord))).val =
        (payloadAt (runtimeAt depth)).sourceState := by
  rw [first_read_source, stage_reads_installed_payload]
  rfl

theorem last_actual_read (depth bound : Nat) :
    (residualEquivRange (lastEvaluator depth bound)
      (lastMap depth bound (prefixSource depth bound OperationRelations.operationWord))).val =
        (payloadAt ((runtimeAt depth).advance bound)).targetState := by
  rw [last_read_source, stage_reads_installed_payload]
  have receipt := stage_state_from_derivation
    ((materialHistory depth bound).stageAt (Fin.last bound))
  dsimp only at receipt
  rw [(stageDerivation ((materialHistory depth bound).stageAt (Fin.last bound))).sound] at receipt
  exact receipt

theorem whole_prefix_factorizes (depth bound : Nat) (index : Fin (bound + 1)) :
    let stage := (materialHistory depth bound).stageAt index
    let runtime := (runtimeAt depth).advance index.val
    (prefixData depth).stageRealization bound
        (prefixSource depth bound OperationRelations.operationWord) index =
      ((payloadAt runtime).sourceState, (payloadAt runtime).forcedTrace) ∧
    (runtimeFacade.readoutAt runtime .particleWave =
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
      stage.next.current = stage.activated.nextCurrent) := by
  have source := stage_source_factorizes ((materialHistory depth bound).stageAt index)
  exact ⟨(prefix_reads_every_stage depth bound _ index).trans source.1, source.2⟩

theorem actual_history_post (depth bound : Nat) :
    ∃ target ∈ postAlong (firstMap depth bound) (lastMap depth bound)
        {point | point = firstMap depth bound
          (prefixSource depth bound OperationRelations.operationWord)},
      (residualEquivRange (lastEvaluator depth bound) target).val =
        (payloadAt ((runtimeAt depth).advance bound)).targetState :=
  ⟨lastMap depth bound (prefixSource depth bound OperationRelations.operationWord),
    ⟨prefixSource depth bound OperationRelations.operationWord, rfl, rfl⟩,
    last_actual_read depth bound⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationDynamics
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
