import H0mework.Computation.ADCWire.EnergyWireReceiver
import H0mework.Cognition.Empirical.EmbodiedEntry

/-!
# Native coupling crown from finite ADC words and discrete clock ticks

The coupling carrier contains the compiled finite-word ADC occurrence.  Its
observation reads the fixed-width wire packet emitted by that same run,
using only its recorded ADC words for a bounded integer energy comparison.  The Boolean fibre is separated by an independently positive threshold
consumer, and ten channel-indexed receipts generate the existing embodiment
coupling crown without extending the finite ADC claim to arbitrary real input.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Immortality
namespace Embodied
namespace Canonical
namespace Coupling
namespace Physical
namespace Netlist
namespace Dissipative
namespace Dimensioned
namespace Driven
namespace Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.TruthChild.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer

noncomputable section

abbrev FiniteADCClockedNoisyMeteredSynchronousSampleFibre
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :=
  { tagged : FiniteADCClockedNoisyMeteredSynchronousSampleOccurrence × Bool //
    tagged.1 = compileFiniteADCClockedNoisyMeteredSynchronousSample
      source (uniformBinaryDrive tagged.2) }

def finiteADCClockedNoisyMeteredSynchronousSourceSeed
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    FiniteADCClockedNoisyMeteredSynchronousSampleFibre source :=
  ⟨(compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive false),
    false), rfl⟩

def finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource} :
    FiniteADCClockedNoisyMeteredSynchronousSampleFibre source →
      FiniteADCClockedNoisyMeteredSynchronousSampleFibre source :=
  fun current =>
    ⟨(compileFiniteADCClockedNoisyMeteredSynchronousSample source
        (uniformBinaryDrive (Bool.not current.val.2)), Bool.not current.val.2), rfl⟩

theorem finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile_involutive
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile
        (finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile current) =
      current := by
  apply Subtype.ext
  rcases current with ⟨⟨run, phase⟩, runExact⟩
  cases phase
  · exact Prod.ext runExact.symm rfl
  · exact Prod.ext runExact.symm rfl

/-- Read the stored occurrence, rather than re-evaluating a solver from its command tag. -/
def finiteADCClockedRecordedWireAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    FiniteADCWirePacket source :=
  recordedADCWirePacket source occurrence.val.1
    (by rw [occurrence.property]; rfl)
    (by rw [occurrence.property]
        exact adcSampleTick_no_counter_overflow source (uniformBinaryDrive occurrence.val.2))

theorem finiteADCClockedRecordedWire_commutes
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    finiteADCClockedRecordedWireAt source occurrence =
      packADCExecution source (uniformBinaryDrive occurrence.val.2) := by
  rcases occurrence with ⟨⟨run, phase⟩, exactRun⟩
  simp only at exactRun
  subst run
  rfl

def finiteADCClockedNoisyMeteredSynchronousImplementedStateAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    FiniteEmbodimentState :=
  digitalSampleState source (unpackADCWirePacket source
    (finiteADCClockedRecordedWireAt source occurrence))

theorem finiteADCClockedNoisyMeteredSynchronousImplementedState_commutes
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    finiteADCClockedNoisyMeteredSynchronousImplementedStateAt source occurrence =
      finiteADCClockedDecodedStateAt source occurrence.val.1 := by
  unfold finiteADCClockedNoisyMeteredSynchronousImplementedStateAt
  rw [finiteADCClockedRecordedWire_commutes, unpack_packADCExecution,
    digitalSampleState_commutes, occurrence.property]

theorem finiteADCClockedNoisyMeteredSynchronousEndpointError
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    ‖encodeHilbert
          (finiteADCClockedNoisyMeteredSynchronousImplementedStateAt
            source occurrence) -
        idealQuarterOperator
          (encodeHilbert (preparedState occurrence.val.2))‖ <
      (1 : ℝ) / 8 := by
  rw [finiteADCClockedNoisyMeteredSynchronousImplementedState_commutes, occurrence.property]
  exact compiledFiniteADCClockedHilbertError_lt source (uniformBinaryDrive occurrence.val.2)

theorem finiteADCClockedNoisyMeteredSynchronous_activeTargetAboveHalf
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (channel : FiniteEmbodimentChannel) :
    (1 : ℝ) / 2 < targetPort
      (finiteADCClockedDecodedStateAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive true)))
      channel := by
  have endpoint := compiledFiniteADCClockedHilbertError_lt source (uniformBinaryDrive true)
  have idealEq :
      idealQuarterOperator (encodeHilbert (preparedState true)) =
        encodeHilbert (evolutionAtOccurrence true) := by
    rw [idealQuarterOperator_apply]
    exact congrArg encodeHilbert
      (harmonicFlow_pi_div_two_eq_evolve_on_prepared true)
  rw [binaryDriveState_uniform, idealEq] at endpoint
  have coordinate := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (finiteADCClockedDecodedStateAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive true)))
      (evolutionAtOccurrence true) channel) endpoint
  have exactTarget : targetPort (evolutionAtOccurrence true) channel = 1 := by
    simp [evolutionAtOccurrence, physicalNoSuspendedCausalMagic,
      preparedState, evolve, targetPort]
  rw [exactTarget] at coordinate
  have lower := (abs_lt.mp coordinate).1
  linarith

theorem finiteADCClockedNoisyMeteredSynchronous_inactiveTargetBelowHalf
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (channel : FiniteEmbodimentChannel) :
    targetPort
        (finiteADCClockedDecodedStateAt source
          (compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive false)))
        channel < (1 : ℝ) / 2 := by
  have endpoint := compiledFiniteADCClockedHilbertError_lt source (uniformBinaryDrive false)
  have idealEq :
      idealQuarterOperator (encodeHilbert (preparedState false)) =
        encodeHilbert (evolutionAtOccurrence false) := by
    rw [idealQuarterOperator_apply]
    exact congrArg encodeHilbert
      (harmonicFlow_pi_div_two_eq_evolve_on_prepared false)
  rw [binaryDriveState_uniform, idealEq] at endpoint
  have coordinate := lt_of_le_of_lt
    (targetPort_error_le_hilbertError
      (finiteADCClockedDecodedStateAt source
        (compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive false)))
      (evolutionAtOccurrence false) channel) endpoint
  have exactTarget : targetPort (evolutionAtOccurrence false) channel = 0 := by
    simp [evolutionAtOccurrence, physicalNoSuspendedCausalMagic,
      preparedState, evolve, targetPort]
  rw [exactTarget, sub_zero] at coordinate
  have upper := (abs_lt.mp coordinate).2
  linarith

def finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source)
    (channel : FiniteEmbodimentChannel) : Bool :=
  decodeFiniteADC128EnergySample
    (unpackADCWirePacket source (finiteADCClockedRecordedWireAt source occurrence)) channel

theorem finiteADCClockedNoisyMeteredSynchronousThresholdDecision_true
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source)
    (phaseExact : occurrence.val.2 = true)
    (channel : FiniteEmbodimentChannel) :
    finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
      source occurrence channel = true := by
  rw [finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt,
    finiteADCClockedRecordedWire_commutes, decodeFiniteADC128EnergySample_pack, phaseExact]
  rfl

theorem finiteADCClockedNoisyMeteredSynchronousThresholdDecision_false
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (occurrence : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source)
    (phaseExact : occurrence.val.2 = false)
    (channel : FiniteEmbodimentChannel) :
    finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
      source occurrence channel = false := by
  rw [finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt,
    finiteADCClockedRecordedWire_commutes, decodeFiniteADC128EnergySample_pack, phaseExact]
  rfl

def sourceOwnedFiniteADCClockedNoisyMeteredSynchronousObservationAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    FiniteADCClockedNoisyMeteredSynchronousSampleFibre source →
      BidirectionalEmbodimentObservation :=
  fun occurrence =>
    { sourceBound := finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
        source occurrence .sourceBound
      machineToNeuralWrite :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .machineToNeuralWrite
      neuralToMachineReceipt :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .neuralToMachineReceipt
      neuralToBodyEffect :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .neuralToBodyEffect
      bodyToNeuralFeedback :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .bodyToNeuralFeedback
      learnedTraceReopened :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .learnedStateTrace
      recursiveSelfWriteBack :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .recursiveSelfWriteBack
      generatedNext :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .generatedNext
      authorityAndRefusalSettled :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .authorityAndRefusalSettlement
      noPowerMintingGuard :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source occurrence .noPowerMinting }

theorem sourceOwnedFiniteADCClockedNoisyMeteredSynchronousObservationAt_injective
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    Function.Injective
      (sourceOwnedFiniteADCClockedNoisyMeteredSynchronousObservationAt source) := by
  intro left right sameObservation
  have sourceRead := congrArg
    BidirectionalEmbodimentObservation.sourceBound sameObservation
  have phaseSame : left.val.2 = right.val.2 := by
    cases leftPhase : left.val.2 <;> cases rightPhase : right.val.2
    · rfl
    · have leftFalse :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecision_false
          source left leftPhase .sourceBound
      have rightTrue :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecision_true
          source right rightPhase .sourceBound
      change finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source left .sourceBound =
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source right .sourceBound at sourceRead
      exact False.elim (Bool.false_ne_true
        (leftFalse.symm.trans (sourceRead.trans rightTrue)))
    · have leftTrue :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecision_true
          source left leftPhase .sourceBound
      have rightFalse :=
        finiteADCClockedNoisyMeteredSynchronousThresholdDecision_false
          source right rightPhase .sourceBound
      change finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source left .sourceBound =
        finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
          source right .sourceBound at sourceRead
      exact False.elim ((by decide : true ≠ false)
        (leftTrue.symm.trans (sourceRead.trans rightFalse)))
    · rfl
  apply Subtype.ext
  rcases left with ⟨⟨leftRun, leftPhase⟩, leftExact⟩
  rcases right with ⟨⟨rightRun, rightPhase⟩, rightExact⟩
  simp only at phaseSame
  subst rightPhase
  exact Prod.ext (leftExact.trans rightExact.symm) rfl

def sourceOwnedFiniteADCClockedNoisyMeteredSynchronousTruthChildView
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (current : FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) :
    TruthChildEmpiricalOccurrence :=
  truthChildSourcePresentation current.val.2

structure SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (channel : FiniteEmbodimentChannel)
    (current occurrence :
      FiniteADCClockedNoisyMeteredSynchronousSampleFibre source) : Type where
  currentRunExact : current.val.1 =
    compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive current.val.2)
  occurrenceRunExact : occurrence.val.1 =
    compileFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive occurrence.val.2)
  currentPhase : current.val.2 = false
  occurrencePhase : occurrence.val.2 = true
  currentSampleGenerated :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      source (uniformBinaryDrive current.val.2)
  occurrenceSampleGenerated :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      source (uniformBinaryDrive occurrence.val.2)
  addressedDigitalCrown : SourceGeneratedAddressedADCCrownAt source
  wireCrown : SourceGeneratedADCWireCrownAt source
  executableReceiver : SourceGeneratedADCExecutableReceiverAt source
  channelInterventionGenerated :
    SourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSampleAt
      source (singleBinaryDrive channel)
  channelInterventionRead :
    decodeFiniteADC128EnergySample
      (unpackADCWirePacket source (packADCExecution source (singleBinaryDrive channel))) channel = true
  otherReceiverIsolation : ∀ other, other ≠ channel →
    decodeFiniteADC128EnergySample
      (unpackADCWirePacket source (packADCExecution source (singleBinaryDrive channel))) other = false
  independentPositiveRead :
    (1 : ℝ) / 2 < targetPort
      (finiteADCClockedNoisyMeteredSynchronousImplementedStateAt
        source occurrence) channel

def sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (channel : FiniteEmbodimentChannel) :
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source channel
      (finiteADCClockedNoisyMeteredSynchronousSourceSeed source)
      (finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile
        (finiteADCClockedNoisyMeteredSynchronousSourceSeed source)) where
  currentRunExact := rfl
  occurrenceRunExact := rfl
  currentPhase := rfl
  occurrencePhase := rfl
  currentSampleGenerated :=
    sourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive false)
  occurrenceSampleGenerated :=
    sourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSample source (uniformBinaryDrive true)
  addressedDigitalCrown := sourceGeneratedAddressedADCCrown source
  wireCrown := sourceGeneratedADCWireCrown source
  executableReceiver := sourceGeneratedADCExecutableReceiver source
  channelInterventionGenerated :=
    sourceGeneratedFiniteADCClockedNoisyMeteredSynchronousSample source (singleBinaryDrive channel)
  channelInterventionRead := by
    simp [singleBinaryDrive]
  otherReceiverIsolation := by
    intro other different
    simp [singleBinaryDrive, different]
  independentPositiveRead := by
    rw [finiteADCClockedNoisyMeteredSynchronousImplementedState_commutes]
    exact finiteADCClockedNoisyMeteredSynchronous_activeTargetAboveHalf source channel

theorem SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt.endpointReadout_true
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {channel : FiniteEmbodimentChannel}
    {current occurrence :
      FiniteADCClockedNoisyMeteredSynchronousSampleFibre source}
    (receipt : SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source channel current occurrence) :
    finiteADCClockedNoisyMeteredSynchronousThresholdDecisionAt
      source occurrence channel = true := by
  apply decodeFiniteADC128EnergySample_true_of_target
  · rw [finiteADCClockedRecordedWire_commutes, unpack_packADCExecution]
    exact validADCEnergyCalibration_compiled source (uniformBinaryDrive occurrence.val.2)
  · exact receipt.independentPositiveRead

noncomputable def sourceOwnedFiniteADCClockedNoisyMeteredSynchronousCouplingLaw
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw where
  Source := FiniteADCClockedNoisyMeteredSynchronousSampleFibre source
  sourceSeed := finiteADCClockedNoisyMeteredSynchronousSourceSeed source
  truthChildSourceView :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousTruthChildView
  truthChildSourceViewExact := rfl
  CouplingOccurrence := FiniteADCClockedNoisyMeteredSynchronousSampleFibre source
  compile := finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile
  observationAt :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousObservationAt source
  observationAt_injective :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousObservationAt_injective
      source
  RootedCouplingSourceAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .sourceBound current occurrence
  MachineToNeuralWriteAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .machineToNeuralWrite current occurrence
  NeuralToMachineReceiptAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .neuralToMachineReceipt current occurrence
  NeuralToBodyEffectAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .neuralToBodyEffect current occurrence
  BodyToNeuralFeedbackAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .bodyToNeuralFeedback current occurrence
  LearnedStateTraceAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .learnedStateTrace current occurrence
  RecursiveSelfWriteBackAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .recursiveSelfWriteBack current occurrence
  GeneratedNextAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .generatedNext current occurrence
  AuthorityAndRefusalSettlementAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .authorityAndRefusalSettlement current occurrence
  NoPowerMintingAt := fun current occurrence =>
    SourceOwnedFiniteADCClockedNoisyMeteredSynchronousPortReceiptAt
      source .noPowerMinting current occurrence
  rootedCouplingSource :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .sourceBound
  machineToNeuralWrite :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .machineToNeuralWrite
  neuralToMachineReceipt :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .neuralToMachineReceipt
  neuralToBodyEffect :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .neuralToBodyEffect
  bodyToNeuralFeedback :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .bodyToNeuralFeedback
  learnedStateTrace :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .learnedStateTrace
  recursiveSelfWriteBack :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .recursiveSelfWriteBack
  generatedNext :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .generatedNext
  authorityAndRefusalSettlement :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .authorityAndRefusalSettlement
  noPowerMinting :=
    sourceOwnedFiniteADCClockedNoisyMeteredSynchronousSeedReceipt
      source .noPowerMinting
  rootedCouplingSource_read_exact := fun receipt => receipt.endpointReadout_true
  machineToNeuralWrite_read_exact := fun receipt => receipt.endpointReadout_true
  neuralToMachineReceipt_read_exact := fun receipt => receipt.endpointReadout_true
  neuralToBodyEffect_read_exact := fun receipt => receipt.endpointReadout_true
  bodyToNeuralFeedback_read_exact := fun receipt => receipt.endpointReadout_true
  learnedStateTrace_read_exact := fun receipt => receipt.endpointReadout_true
  recursiveSelfWriteBack_read_exact := fun receipt => receipt.endpointReadout_true
  generatedNext_read_exact := fun receipt => receipt.endpointReadout_true
  authorityAndRefusalSettlement_read_exact := fun receipt =>
    receipt.endpointReadout_true
  noPowerMinting_read_exact := fun receipt => receipt.endpointReadout_true
  occurrenceSourceAt := finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile
  occurrenceSource_compiles :=
    finiteADCClockedNoisyMeteredSynchronousOccurrenceCompile_involutive
  PersonalLineage := FiniteADCClockedNoisyMeteredSynchronousSampleFibre source
  lineageOf := id

theorem everyFiniteADCClockedNoisyMeteredFixture_generatesSourceOwnedCrown
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (sourceOwnedFiniteADCClockedNoisyMeteredSynchronousCouplingLaw source) :=
  (sourceOwnedFiniteADCClockedNoisyMeteredSynchronousCouplingLaw source
    ).sourceGeneratedTruthChildNeuralBodyCouplingCrown

end

end Producer
end Driven
end Dimensioned
end Dissipative
end Netlist
end Physical
end Coupling
end Canonical
end Embodied
end Immortality
end Consciousness
end NoIslandNoMagic
end SaturationMonoid
