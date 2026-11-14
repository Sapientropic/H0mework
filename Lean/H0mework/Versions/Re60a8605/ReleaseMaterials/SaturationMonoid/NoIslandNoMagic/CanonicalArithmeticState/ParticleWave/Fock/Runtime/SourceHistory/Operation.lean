import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Probability.Source.Full.Binary
import H0mework.Versions.Re60a8605.Probability.FullSource.Readout
import H0mework.Fock.SourceHistory.Projection

/-! The original unit-history primitive acts on the whole source field and feeds its installed write. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory.FullBinary.Fock

open SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open ArithmeticGeneration

noncomputable section

def parallel := binary nativeStep nativeStep nativeStep UnitHistory.parallel

private theorem raw_parallel_unit (value : Carrier Current) :
    SourceNativeBinary.linear UnitHistory.parallel value (sourcePoint CanonicalUnitArithmeticRoot.unitHistory) =
      sourceAction nativeStep value := by
  have same : (SourceNativeBinary.linear UnitHistory.parallel).flip
      (sourcePoint CanonicalUnitArithmeticRoot.unitHistory) = sourceAction nativeStep := by
    apply Finsupp.lhom_ext'
    intro current
    apply LinearMap.ext_ring
    change SourceNativeBinary.lift UnitHistory.parallel (sourcePoint current)
      (sourcePoint CanonicalUnitArithmeticRoot.unitHistory) = sourceAction nativeStep (sourcePoint current)
    exact (SourceNativeBinary.lift_point UnitHistory.parallel current CanonicalUnitArithmeticRoot.unitHistory).trans
      (sourceAction_point nativeStep current).symm
  exact LinearMap.congr_fun same value

theorem parallel_unit_action (value : Field nativeStep fullRead) :
    parallel value (fieldPoint nativeStep fullRead CanonicalUnitArithmeticRoot.unitHistory) =
      fieldAction nativeStep fullRead value := by
  apply FullWord.word_injective nativeStep
  change FullWord.word nativeStep (binary nativeStep nativeStep nativeStep UnitHistory.parallel value _) = _
  rw [binary_word, FullWord.word_point, FullWord.word_action]
  exact raw_parallel_unit _

theorem state_projection_action (value : Field nativeStep fullRead) :
    FullProjection.Fock.stateProjection (fieldAction nativeStep fullRead value) =
      observation sourceStateAt (sourceAction nativeStep (FullWord.word nativeStep value)) := by
  change FullProjection.readNow nativeStep sourceStateAt (fieldAction nativeStep fullRead value) = _
  rw [FullWord.readNow_word, FullWord.word_action]

variable {current : Current}
variable {occurrence : BaseLedgerSource.source.toRootSource.actual.OccurrenceAt current}
variable {active : 1 ≤ scanIndex current}
variable (payload : RootGeneratedParticleWaveCurrentAt current occurrence active)

theorem parallel_written :
    parallel (fieldPoint nativeStep fullRead current)
        (fieldPoint nativeStep fullRead CanonicalUnitArithmeticRoot.unitHistory) =
      fieldPoint nativeStep fullRead payload.nativeWrite.target :=
  (parallel_unit_action _).trans (native_field_point payload)

theorem runtime_parallel_factorizes (depth : Nat) (value : Field nativeStep fullRead) :
    let runtime := runtimeAt depth
    let stage := SourceGeneratedRuntimeMaterialStageAt.generate runtime
    parallel value (fieldPoint nativeStep fullRead CanonicalUnitArithmeticRoot.unitHistory) =
        fieldAction nativeStep fullRead value ∧
      parallel (fieldPoint nativeStep fullRead runtime.current.visit.current)
          (fieldPoint nativeStep fullRead CanonicalUnitArithmeticRoot.unitHistory) =
        fieldPoint nativeStep fullRead (runtimePayload depth).nativeWrite.target ∧
      FullProjection.Fock.stateProjection
          (parallel (fieldPoint nativeStep fullRead runtime.current.visit.current)
            (fieldPoint nativeStep fullRead CanonicalUnitArithmeticRoot.unitHistory)) =
        (runtimePayload depth).sourceState + (runtimePayload depth).forcedTrace ∧
      (runtimePayload depth).sourceOccurrence = runtime.emittedOccurrence ∧
      HEq (runtimeFacade.readoutAt runtime .particleWave)
        (stage.activated.generated.projectionOutcome
          ((runtimeFacade.installationAt runtime .particleWave).embed
            (runtimeFacade.projectionAt runtime .particleWave))) ∧
      (runtimeFacade.process.toAnswerNextCausalWorld.emitted (ULift.up runtime.state) =
          ULift.up stage.activated.generated ∧
        stage.activated.generated.occurrence =
          runtime.current.root.toAuthoritativeRoot.toLedgerRoot.emitted runtime.current.visit.current ∧
        HEq stage.wholeLedgerWriteBack
          (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
        stage.next.current = stage.activated.nextCurrent) ∧
      stage.next.current.visit.current = (runtimePayload depth).nativeWrite.target := by
  have installed := coversAt_factorizes (runtimeAt depth) .particleWave
  have effect := FullProjection.Fock.stateProjection_effect (runtimePayload depth)
  rw [FullProjection.Fock.stateProjection_source (runtimePayload depth)] at effect
  refine ⟨parallel_unit_action value, parallel_written (runtimePayload depth), ?_,
    (runtimePayload depth).sourceOccurrence_eq, installed.2.2.2.1,
    (SourceGeneratedRuntimeMaterialStageAt.generate (runtimeAt depth)).factorizes, runtime_current_next depth⟩
  exact (congrArg FullProjection.Fock.stateProjection (parallel_unit_action _)).trans effect

end
end SourceOwnedObservationHistory.FullBinary.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
