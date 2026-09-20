import H0mework.Realization.Operations.CochainComplex
import H0mework.Fock.Cofinal.OperationEnvelopeReadout

/-! The original material stages generate cochains and read their state equations through the exact envelope. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationCochain

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open SourceOperationEffects SourceOperationRelations SourceOperationCochain

noncomputable section

abbrev ChangedCarrier := Formal OperationValue (ChangedVar OperationVar) .parent

def stageComplex {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :=
  cochain (s := OperationSort.parent) (oldEnvironment stage) (incrementEnvironment stage)

theorem stage_updated_read {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    (updated fockOperation).eval
        (mixedEnvironment (oldEnvironment stage) (incrementEnvironment stage)) =
      (payloadAt runtime).targetState := by
  rw [eval_updated]
  have environment : oldEnvironment stage + incrementEnvironment stage =
      fieldEnvironment (sourceFieldAt stage.next.current.visit.current) := by
    unfold oldEnvironment incrementEnvironment
    rw [fieldEnvironment_add]
    congr 1
    abel
  rw [environment, fockOperation_eval, (payloadAt runtime).targetState_eq]
  rfl

theorem stage_old_read {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    fockOperation.old.eval
        (mixedEnvironment (oldEnvironment stage) (incrementEnvironment stage)) =
      (payloadAt runtime).sourceState := by
  rw [Expr.eval_old, (payloadAt runtime).sourceState_eq]
  rfl

theorem stage_trace_read {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    evaluation (s := OperationSort.parent)
      (mixedEnvironment (oldEnvironment stage) (incrementEnvironment stage))
        (traceWord fockOperation.mixedTerms) = (payloadAt runtime).forcedTrace := by
  rw [evaluation_traceWord, Expr.mixedTerms_sum, (payloadAt runtime).forcedTrace_eq]
  rfl

theorem stage_boundary_read {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    evaluation (s := OperationSort.parent)
      (mixedEnvironment (oldEnvironment stage) (incrementEnvironment stage))
        (boundary OperationRelations.operationWord) =
      (payloadAt runtime).targetState - (payloadAt runtime).sourceState -
        (payloadAt runtime).forcedTrace := by
  unfold OperationRelations.operationWord
  rw [boundary_single, one_smul, updateWord, map_sub, map_sub, stage_trace_read]
  simp only [evaluation, Finsupp.linearCombination_single, one_smul]
  rw [stage_updated_read, stage_old_read]

/-- The original state equation is read from the source-generated cochain boundary. -/
theorem stage_state_from_boundary {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    (payloadAt runtime).targetState =
      (payloadAt runtime).sourceState + (payloadAt runtime).forcedTrace := by
  have generated := LinearMap.congr_fun
    (evaluation_boundary (s := OperationSort.parent) (oldEnvironment stage)
      (incrementEnvironment stage)) OperationRelations.operationWord
  change evaluation _ (boundary OperationRelations.operationWord) = 0 at generated
  rw [stage_boundary_read, sub_sub, sub_eq_zero] at generated
  exact generated

theorem stage_cochain_factorizes {runtime : LivingRuntimeState runtimeFacade.process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    ((stageComplex stage).d 0 1).hom OperationRelations.operationWord =
      updateWord fockOperation ∧
    (payloadAt runtime).targetState =
      (payloadAt runtime).sourceState + (payloadAt runtime).forcedTrace ∧
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
  have source := stage_source_factorizes stage
  refine ⟨?_, stage_state_from_boundary stage, source.2⟩
  simp only [stageComplex, cochain_d₀]
  change boundary OperationRelations.operationWord = updateWord fockOperation
  unfold OperationRelations.operationWord
  rw [boundary_single, one_smul]

theorem envelope_state_from_boundary (depth bound : Nat) (index : Fin (bound + 1)) :
    let seen := ParticleWaveFockOperationEnvelope.envelopeStageRead depth bound
      (ParticleWaveFockOperationEnvelope.sourceMap depth OperationRelations.operationWord) index
    (payloadAt ((runtimeAt depth).advance index.val)).targetState = seen.1 + seen.2 := by
  dsimp only
  rw [(ParticleWaveFockOperationEnvelope.envelope_word_factorizes depth bound index).1]
  exact stage_state_from_boundary ((materialHistory depth bound).stageAt index)

theorem envelope_inverse_fibre_from_boundary (depth bound : Nat) (index : Fin (bound + 1))
    (alternative : ParentCarrier) :
    let seen := ParticleWaveFockOperationEnvelope.envelopeStageRead depth bound
      (ParticleWaveFockOperationEnvelope.sourceMap depth OperationRelations.operationWord) index
    jointMeasurement alternative =
        jointMeasurement (payloadAt ((runtimeAt depth).advance index.val)).targetState ↔
      alternative - (seen.1 + seen.2) ∈ JointMeasurementKernel := by
  dsimp only
  rw [← envelope_state_from_boundary depth bound index]
  exact (payloadAt ((runtimeAt depth).advance index.val)).inverseFibreLaw alternative

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationCochain
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
