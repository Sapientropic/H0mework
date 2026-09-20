import H0mework.Fock.Cofinal.OperationEnvelope

/-! Original state and measurement consumers of the source-generated exact envelope. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationEnvelope

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open SourceOperationEffects SourceOperationRelations

noncomputable section

theorem envelope_target_read (depth bound : Nat) (index : Fin (bound + 1)) :
    let seen := envelopeStageRead depth bound (sourceMap depth OperationRelations.operationWord) index
    seen.1 + seen.2 = (payloadAt ((runtimeAt depth).advance index.val)).targetState := by
  dsimp only
  rw [(envelope_word_factorizes depth bound index).1]
  exact (payloadAt ((runtimeAt depth).advance index.val)).stateUpdate.symm

theorem envelope_measurement_read (depth bound : Nat) (index : Fin (bound + 1)) :
    let seen := envelopeStageRead depth bound (sourceMap depth OperationRelations.operationWord) index
    jointMeasurement (payloadAt ((runtimeAt depth).advance index.val)).targetState =
      jointMeasurement seen.1 + jointMeasurement seen.2 := by
  dsimp only
  rw [(envelope_word_factorizes depth bound index).1]
  exact (payloadAt ((runtimeAt depth).advance index.val)).measurementUpdate

theorem envelope_coimage_read (depth bound : Nat) (index : Fin (bound + 1)) :
    let seen := envelopeStageRead depth bound (sourceMap depth OperationRelations.operationWord) index
    jointMeasurementCoimage (payloadAt ((runtimeAt depth).advance index.val)).targetState =
      jointMeasurementCoimage seen.1 + jointMeasurementCoimage seen.2 := by
  dsimp only
  rw [(envelope_word_factorizes depth bound index).1]
  exact (payloadAt ((runtimeAt depth).advance index.val)).coimageUpdate

theorem source_coevaluation_roundtrip (depth : Nat) (word : FormalCarrier) :
    (generatedEnvelope depth).coevaluation ((generatedEnvelope depth).map (sourceMap depth word)) =
      sourceMap depth word :=
  (generatedEnvelope depth).equivalence.symm_apply_apply (sourceMap depth word)


end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationEnvelope
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
