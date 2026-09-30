import H0mework.Realization.Operations.FieldInputs
import H0mework.Versions.X.Fock.Cofinal.OperationPrefix

/-! The original particle-wave materialization consumes the generated full-state native action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockNativeConsumer

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open SourceOperationNative

noncomputable section

def sourceRead (state : process.State) : ParentCarrier :=
  sourceStateAt (finiteVisit state).current

def materialization : SourceOperationNative.Carrier process →ₗ[ℤ] ParentCarrier :=
  observer process sourceRead

theorem materialization_current (runtime : LivingRuntimeState process) :
    materialization (point runtime) = (payloadAt runtime).sourceState := by
  rw [materialization, observer_point, (payloadAt runtime).sourceState_eq]
  rfl

theorem materialization_next (runtime : LivingRuntimeState process) :
    materialization (point runtime.tick.next) = (payloadAt runtime).targetState := by
  rw [materialization, observer_point, (payloadAt runtime).targetState_eq]
  rfl

theorem native_field_target (depth bound : Nat) (index : Fin (bound + 1)) :
    materialization
        (SourceOperationNative.Field.read (runtimeAt depth) bound
          (SourceOperationNative.Field.actionValue (runtimeAt depth)) index).1 =
      (payloadAt ((runtimeAt depth).advance index.val)).targetState := by
  have fieldRead := SourceOperationNative.Field.actionValue_read
    (process := process) (runtimeAt depth) bound index
  have pointRead := congrArg (Prod.fst : SourceOperationNative.Carrier process ×
    SourceOperationNative.Carrier process → SourceOperationNative.Carrier process) fieldRead
  exact (congrArg materialization pointRead).trans
    (materialization_next ((runtimeAt depth).advance index.val))

theorem native_witness_target (depth bound : Nat) (index : Fin (bound + 1)) :
    (SourceOperationNative.Field.nextWitness (runtimeAt depth) bound index).1.current.visit.current =
      (payloadAt ((runtimeAt depth).advance index.val)).nativeWrite.target :=
  material_next_is_native_target ((materialHistory depth bound).stageAt index)

theorem native_readout_is_original_write_target (depth bound : Nat) (index : Fin (bound + 1)) :
    (SourceOperationNative.Field.nativeReadWitness (fun state => (finiteVisit state).current)
      (runtimeAt depth) bound index).1 =
        (payloadAt ((runtimeAt depth).advance index.val)).nativeWrite.target :=
  native_witness_target depth bound index

theorem native_field_factorizes (depth bound : Nat) (index : Fin (bound + 1)) :
    let stage := (materialHistory depth bound).stageAt index
    let runtime := (runtimeAt depth).advance index.val
    (SourceOperationNative.Field.nextWitness (runtimeAt depth) bound index).1 = stage.next ∧
    materialization
        (SourceOperationNative.Field.read (runtimeAt depth) bound
          (SourceOperationNative.Field.actionValue (runtimeAt depth)) index).1 =
      (payloadAt runtime).targetState ∧
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
  exact ⟨SourceOperationNative.Field.nextWitness_is_actual (runtimeAt depth) bound index,
    native_field_target depth bound index,
    (stage_source_factorizes ((materialHistory depth bound).stageAt index)).2⟩

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockNativeConsumer
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
