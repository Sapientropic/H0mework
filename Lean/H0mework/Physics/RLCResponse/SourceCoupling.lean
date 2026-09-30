import H0mework.Physics.RLCResponse.ResonantCoupling
import H0mework.Physics.PortCoupling.CertifiedTolerance

/-!
# Source-owned resonant driven series-RLC coupling

The source is exactly the carrier consumed by the driven circuit: ten finite
frequency symbols and one positive SI scale triple.  Legacy transient gain,
clock, crosstalk and bias coordinates are not present.  Compilation generates
the dimensioned R/L/C run, each channel's natural drive frequency, and the
actual inductor-output voltage scale.  No response, receipt or crown is a run
field.

Every observation is evaluated from that compiled run: voltage drive,
capacitor response, current, inductor component voltage and output-scale
normalization.  Ten receipts retain the periodic circuit law, exact resistor
half-power band and inductor-phase commuting.  Their readout proof explicitly
uses that physical commuting before consuming the generic ideal threshold
receipt; the final crown is native to this run-bearing law.
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
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

/-! ## Minimal driven-core source -/

abbrev ResonantDrivenCoreCode :=
  FiniteEmbodimentChannel → TernaryCalibrationOffset

abbrev ResonantDrivenCoreSource :=
  ResonantDrivenCoreCode × PositiveElectricalScale

def resonantDrivenZeroOffsetWord :
    FiniteEmbodimentChannel → TernaryCalibrationOffset := fun _ => .zero

/-- Canonical embedding into the already certified dimensioned RLC compiler.
Only the frequency word is variable; irrelevant legacy endpoint coordinates
are fixed before compilation and are not part of the driven source type. -/
def resonantDrivenCoreDimensionedSource
    (source : ResonantDrivenCoreSource) : DimensionedSeriesRLCSource :=
  ((((source.1, resonantDrivenZeroOffsetWord), .zero), .zero), source.2)

theorem resonantDrivenCoreDimensionedSource_injective :
    Function.Injective resonantDrivenCoreDimensionedSource := by
  intro left right sameSource
  apply Prod.ext
  · exact congrArg (fun source : DimensionedSeriesRLCSource =>
      source.1.1.1.1) sameSource
  · exact congrArg (fun source : DimensionedSeriesRLCSource => source.2)
      sameSource

/-- Literal source-only driven run.  Every field below is consumed by the
run-level output calculation. -/
structure FiniteResonantDrivenSeriesRLCRunOccurrence where
  dimensionedRun : FiniteDimensionedSeriesRLCNetlistRunOccurrence
  driveFrequencyAt : FiniteEmbodimentChannel → SIHertz
  outputVoltageScaleAt : FiniteEmbodimentChannel → SIVolt

def compileFiniteResonantDrivenSeriesRLCRun
    (source : ResonantDrivenCoreSource) :
    FiniteResonantDrivenSeriesRLCRunOccurrence :=
  let physicalSource := resonantDrivenCoreDimensionedSource source
  { dimensionedRun := compileFiniteDimensionedSeriesRLCNetlistRun physicalSource
    driveFrequencyAt := drivenNaturalAngularFrequencyAt physicalSource
    outputVoltageScaleAt := resonantInductorOutputScaleAt physicalSource }

theorem compileFiniteResonantDrivenSeriesRLCRun_injective :
    Function.Injective compileFiniteResonantDrivenSeriesRLCRun := by
  intro left right sameRun
  apply resonantDrivenCoreDimensionedSource_injective
  apply compileFiniteDimensionedSeriesRLCNetlistRun_injective
  exact congrArg FiniteResonantDrivenSeriesRLCRunOccurrence.dimensionedRun
    sameRun

/-! ## Every calculation reads the compiled run -/

def resonantDrivenRunDrivePhasorAt
    (run : FiniteResonantDrivenSeriesRLCRunOccurrence)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SIVoltagePhasor :=
  voltagePhasorOfNormalized run.dimensionedRun.scale.voltageScale
    (encodePort (state channel))

def resonantDrivenRunCapacitorResponsePhasorAt
    (run : FiniteResonantDrivenSeriesRLCRunOccurrence)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SIVoltagePhasor :=
  drivenVoltageResponseAt run.dimensionedRun channel
    (run.driveFrequencyAt channel)
    (resonantDrivenRunDrivePhasorAt run state channel)

def resonantDrivenRunCurrentPhasorAt
    (run : FiniteResonantDrivenSeriesRLCRunOccurrence)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SICurrentPhasor :=
  drivenCapacitorCurrentPhasorAt run.dimensionedRun channel
    (run.driveFrequencyAt channel)
    (resonantDrivenRunCapacitorResponsePhasorAt run state channel)

def resonantDrivenRunInductorVoltagePhasorAt
    (run : FiniteResonantDrivenSeriesRLCRunOccurrence)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) :
    SIVoltagePhasor :=
  drivenInductorVoltagePhasorAt run.dimensionedRun channel
    (run.driveFrequencyAt channel)
    (resonantDrivenRunCurrentPhasorAt run state channel)

def resonantDrivenRunPortOutputAt
    (run : FiniteResonantDrivenSeriesRLCRunOccurrence)
    (state : FiniteEmbodimentState) (channel : FiniteEmbodimentChannel) : ℂ :=
  normalizeVoltagePhasor (run.outputVoltageScaleAt channel)
    (resonantDrivenRunInductorVoltagePhasorAt run state channel)

def resonantDrivenRunHilbertOutputAt
    (run : FiniteResonantDrivenSeriesRLCRunOccurrence)
    (state : FiniteEmbodimentState) : HilbertEmbodimentState :=
  WithLp.toLp 2 (fun channel =>
    resonantDrivenRunPortOutputAt run state channel)

theorem compiledResonantDrivenRunHilbertOutput_eq_physical
    (source : ResonantDrivenCoreSource) (state : FiniteEmbodimentState) :
    resonantDrivenRunHilbertOutputAt
        (compileFiniteResonantDrivenSeriesRLCRun source) state =
      resonantDrivenHilbertOutputAt
        (resonantDrivenCoreDimensionedSource source) state :=
  rfl

theorem compiledResonantDrivenRunHilbertOutput_eq_ideal
    (source : ResonantDrivenCoreSource) (state : FiniteEmbodimentState) :
    resonantDrivenRunHilbertOutputAt
        (compileFiniteResonantDrivenSeriesRLCRun source) state =
      idealQuarterOperator (encodeHilbert state) := by
  rw [compiledResonantDrivenRunHilbertOutput_eq_physical,
    resonantDrivenHilbertOutput_eq_idealQuarter]

/-! ## Fixed-run occurrence fibre and observation -/

abbrev FiniteResonantDrivenSeriesRLCRunFibre
    (source : ResonantDrivenCoreSource) :=
  { tagged : FiniteResonantDrivenSeriesRLCRunOccurrence × Bool //
    tagged.1 = compileFiniteResonantDrivenSeriesRLCRun source }

def finiteResonantDrivenSeriesRLCSourceSeed
    (source : ResonantDrivenCoreSource) :
    FiniteResonantDrivenSeriesRLCRunFibre source :=
  ⟨(compileFiniteResonantDrivenSeriesRLCRun source, false), rfl⟩

def finiteResonantDrivenSeriesRLCOccurrenceCompile
    {source : ResonantDrivenCoreSource} :
    FiniteResonantDrivenSeriesRLCRunFibre source →
      FiniteResonantDrivenSeriesRLCRunFibre source :=
  fun current =>
    ⟨(current.val.1, Bool.not current.val.2), current.property⟩

theorem finiteResonantDrivenSeriesRLCOccurrenceCompile_involutive
    {source : ResonantDrivenCoreSource}
    (current : FiniteResonantDrivenSeriesRLCRunFibre source) :
    finiteResonantDrivenSeriesRLCOccurrenceCompile
        (finiteResonantDrivenSeriesRLCOccurrenceCompile current) = current := by
  apply Subtype.ext
  rcases current with ⟨⟨run, phase⟩, runExact⟩
  cases phase <;> rfl

def resonantDrivenImplementedStateAt
    (source : ResonantDrivenCoreSource) (phase : Bool) :
    FiniteEmbodimentState :=
  decodeHilbert
    (resonantDrivenRunHilbertOutputAt
      (compileFiniteResonantDrivenSeriesRLCRun source) (preparedState phase))

def resonantDrivenThresholdDecisionAt
    (source : ResonantDrivenCoreSource) (phase : Bool)
    (channel : FiniteEmbodimentChannel) : Bool :=
  decide ((1 : ℝ) / 2 <
    targetPort (resonantDrivenImplementedStateAt source phase) channel)

def sourceOwnedResonantDrivenObservationAt
    (source : ResonantDrivenCoreSource) :
    FiniteResonantDrivenSeriesRLCRunFibre source →
      BidirectionalEmbodimentObservation :=
  fun occurrence =>
    { sourceBound := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .sourceBound
      machineToNeuralWrite := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .machineToNeuralWrite
      neuralToMachineReceipt := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .neuralToMachineReceipt
      neuralToBodyEffect := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .neuralToBodyEffect
      bodyToNeuralFeedback := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .bodyToNeuralFeedback
      learnedTraceReopened := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .learnedStateTrace
      recursiveSelfWriteBack := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .recursiveSelfWriteBack
      generatedNext := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .generatedNext
      authorityAndRefusalSettled := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .authorityAndRefusalSettlement
      noPowerMintingGuard := resonantDrivenThresholdDecisionAt
        source occurrence.val.2 .noPowerMinting }

theorem sourceOwnedResonantDrivenObservation_eq_ideal
    (source : ResonantDrivenCoreSource)
    (occurrence : FiniteResonantDrivenSeriesRLCRunFibre source) :
    sourceOwnedResonantDrivenObservationAt source occurrence =
      thresholdObservationAt idealQuarterOperator occurrence.val.2 := by
  have outputCommutes := compiledResonantDrivenRunHilbertOutput_eq_ideal
    source (preparedState occurrence.val.2)
  apply BidirectionalEmbodimentObservation.ext
  all_goals
    simp [sourceOwnedResonantDrivenObservationAt,
      resonantDrivenThresholdDecisionAt, resonantDrivenImplementedStateAt,
      thresholdObservationAt, implementedState, outputCommutes]

theorem sourceOwnedResonantDrivenObservationAt_injective
    (source : ResonantDrivenCoreSource) :
    Function.Injective (sourceOwnedResonantDrivenObservationAt source) := by
  intro left right sameObservation
  have sameIdeal :
      thresholdObservationAt idealQuarterOperator left.val.2 =
        thresholdObservationAt idealQuarterOperator right.val.2 := by
    rw [← sourceOwnedResonantDrivenObservation_eq_ideal,
      ← sourceOwnedResonantDrivenObservation_eq_ideal]
    exact sameObservation
  have phaseSame : left.val.2 = right.val.2 :=
    thresholdObservationAt_injective idealQuarterOperator
      idealQuarterOperator_hasTolerance sameIdeal
  apply Subtype.ext
  exact Prod.ext (left.property.trans right.property.symm) phaseSame

def sourceOwnedResonantDrivenTruthChildView
    {source : ResonantDrivenCoreSource}
    (current : FiniteResonantDrivenSeriesRLCRunFibre source) :
    TruthChildEmpiricalOccurrence :=
  truthChildSourcePresentation current.val.2

/-! ## Ten run-bearing physical receipts -/

structure SourceOwnedResonantDrivenPortReceiptAt
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel)
    (current occurrence : FiniteResonantDrivenSeriesRLCRunFibre source) :
    Type where
  sourceRunExact :
    current.val.1 = compileFiniteResonantDrivenSeriesRLCRun source
  occurrenceRunExact :
    occurrence.val.1 = compileFiniteResonantDrivenSeriesRLCRun source
  occurrencePreservesSourceRun : occurrence.val.1 = current.val.1
  sourceCompilerInjective :
    Function.Injective compileFiniteResonantDrivenSeriesRLCRun
  periodicParticular : ∀ state,
    SourceGeneratedDrivenPeriodicParticularAt
      (resonantDrivenCoreDimensionedSource source) channel
      (drivenNaturalAngularFrequencyAt
        (resonantDrivenCoreDimensionedSource source) channel)
      (resonantDrivePhasorAt
        (resonantDrivenCoreDimensionedSource source) state channel)
  exactHalfPowerBandwidth :
    SourceGeneratedExactHalfPowerBandwidthAt
      (resonantDrivenCoreDimensionedSource source) channel
  resistorSenseIsComponent : ∀ state,
    resistorSenseVoltageResponseAt
        (compileFiniteDimensionedSeriesRLCNetlistRun
          (resonantDrivenCoreDimensionedSource source)) channel
        (drivenNaturalAngularFrequencyAt
          (resonantDrivenCoreDimensionedSource source) channel)
        (resonantDrivePhasorAt
          (resonantDrivenCoreDimensionedSource source) state channel) =
      drivenResistorVoltagePhasorAt
        (compileFiniteDimensionedSeriesRLCNetlistRun
          (resonantDrivenCoreDimensionedSource source)) channel
        (drivenPeriodicCurrentPhasorAt
          (resonantDrivenCoreDimensionedSource source) channel
          (drivenNaturalAngularFrequencyAt
            (resonantDrivenCoreDimensionedSource source) channel)
          (resonantDrivePhasorAt
            (resonantDrivenCoreDimensionedSource source) state channel))
  inductorProducesMinusI : ∀ state,
    resonantInductorVoltagePhasorAt
        (resonantDrivenCoreDimensionedSource source) state channel =
      resonantInductorVoltageRatioAt
          (resonantDrivenCoreDimensionedSource source) channel •
        minusIQuadratureVoltagePhasor
          (resonantDrivePhasorAt
            (resonantDrivenCoreDimensionedSource source) state channel)
  outputScalePositive :
    0 < ((compileFiniteResonantDrivenSeriesRLCRun source
      ).outputVoltageScaleAt channel).value
  runOutputCommutes : ∀ state,
    resonantDrivenRunHilbertOutputAt
        (compileFiniteResonantDrivenSeriesRLCRun source) state =
      idealQuarterOperator (encodeHilbert state)
  operatorPhysical : OperatorTolerancePortReceiptAt idealQuarterOperator
    channel current.val.2 occurrence.val.2

def sourceOwnedResonantDrivenSeedReceipt
    (source : ResonantDrivenCoreSource)
    (channel : FiniteEmbodimentChannel) :
    SourceOwnedResonantDrivenPortReceiptAt source channel
      (finiteResonantDrivenSeriesRLCSourceSeed source)
      (finiteResonantDrivenSeriesRLCOccurrenceCompile
        (finiteResonantDrivenSeriesRLCSourceSeed source)) where
  sourceRunExact := rfl
  occurrenceRunExact := rfl
  occurrencePreservesSourceRun := rfl
  sourceCompilerInjective := compileFiniteResonantDrivenSeriesRLCRun_injective
  periodicParticular := fun state =>
    sourceGeneratedDrivenPeriodicParticular
      (resonantDrivenCoreDimensionedSource source) channel
      (drivenNaturalAngularFrequencyAt
        (resonantDrivenCoreDimensionedSource source) channel)
      (resonantDrivePhasorAt
        (resonantDrivenCoreDimensionedSource source) state channel)
      (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos
        (resonantDrivenCoreDimensionedSource source) channel))
  exactHalfPowerBandwidth := sourceGeneratedExactHalfPowerBandwidth
    (resonantDrivenCoreDimensionedSource source) channel
  resistorSenseIsComponent := fun state =>
    resistorSenseVoltageResponse_eq_resistorComponent
      (resonantDrivenCoreDimensionedSource source) channel
      (drivenNaturalAngularFrequencyAt
        (resonantDrivenCoreDimensionedSource source) channel)
      (Real.sqrt_pos.2 (drivenNaturalFrequencySq_pos
        (resonantDrivenCoreDimensionedSource source) channel))
      (resonantDrivePhasorAt
        (resonantDrivenCoreDimensionedSource source) state channel)
  inductorProducesMinusI := fun state =>
    resonantInductorVoltagePhasor_eq_physicalMinusI
      (resonantDrivenCoreDimensionedSource source) state channel
  outputScalePositive :=
    resonantInductorOutputScale_pos
      (resonantDrivenCoreDimensionedSource source) channel
  runOutputCommutes := compiledResonantDrivenRunHilbertOutput_eq_ideal source
  operatorPhysical :=
    toleranceSeedReceipt idealQuarterOperator idealQuarterOperator_hasTolerance
      channel

theorem SourceOwnedResonantDrivenPortReceiptAt.endpointReadout_true
    {source : ResonantDrivenCoreSource}
    {channel : FiniteEmbodimentChannel}
    {current occurrence : FiniteResonantDrivenSeriesRLCRunFibre source}
    (receipt : SourceOwnedResonantDrivenPortReceiptAt
      source channel current occurrence) :
    resonantDrivenThresholdDecisionAt source occurrence.val.2 channel = true := by
  unfold resonantDrivenThresholdDecisionAt resonantDrivenImplementedStateAt
  rw [receipt.runOutputCommutes]
  exact receipt.operatorPhysical.readout_true

/-! ## Native source-owned law -/

noncomputable def sourceOwnedFiniteResonantDrivenSeriesRLCCouplingLaw
    (source : ResonantDrivenCoreSource) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw where
  Source := FiniteResonantDrivenSeriesRLCRunFibre source
  sourceSeed := finiteResonantDrivenSeriesRLCSourceSeed source
  truthChildSourceView := sourceOwnedResonantDrivenTruthChildView
  truthChildSourceViewExact := rfl
  CouplingOccurrence := FiniteResonantDrivenSeriesRLCRunFibre source
  compile := finiteResonantDrivenSeriesRLCOccurrenceCompile
  observationAt := sourceOwnedResonantDrivenObservationAt source
  observationAt_injective :=
    sourceOwnedResonantDrivenObservationAt_injective source
  RootedCouplingSourceAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .sourceBound current occurrence
  MachineToNeuralWriteAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .machineToNeuralWrite current occurrence
  NeuralToMachineReceiptAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .neuralToMachineReceipt current occurrence
  NeuralToBodyEffectAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .neuralToBodyEffect current occurrence
  BodyToNeuralFeedbackAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .bodyToNeuralFeedback current occurrence
  LearnedStateTraceAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .learnedStateTrace current occurrence
  RecursiveSelfWriteBackAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .recursiveSelfWriteBack current occurrence
  GeneratedNextAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .generatedNext current occurrence
  AuthorityAndRefusalSettlementAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .authorityAndRefusalSettlement current occurrence
  NoPowerMintingAt := fun current occurrence =>
    SourceOwnedResonantDrivenPortReceiptAt
      source .noPowerMinting current occurrence
  rootedCouplingSource :=
    sourceOwnedResonantDrivenSeedReceipt source .sourceBound
  machineToNeuralWrite :=
    sourceOwnedResonantDrivenSeedReceipt source .machineToNeuralWrite
  neuralToMachineReceipt :=
    sourceOwnedResonantDrivenSeedReceipt source .neuralToMachineReceipt
  neuralToBodyEffect :=
    sourceOwnedResonantDrivenSeedReceipt source .neuralToBodyEffect
  bodyToNeuralFeedback :=
    sourceOwnedResonantDrivenSeedReceipt source .bodyToNeuralFeedback
  learnedStateTrace :=
    sourceOwnedResonantDrivenSeedReceipt source .learnedStateTrace
  recursiveSelfWriteBack :=
    sourceOwnedResonantDrivenSeedReceipt source .recursiveSelfWriteBack
  generatedNext :=
    sourceOwnedResonantDrivenSeedReceipt source .generatedNext
  authorityAndRefusalSettlement :=
    sourceOwnedResonantDrivenSeedReceipt source .authorityAndRefusalSettlement
  noPowerMinting :=
    sourceOwnedResonantDrivenSeedReceipt source .noPowerMinting
  rootedCouplingSource_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  machineToNeuralWrite_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  neuralToMachineReceipt_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  neuralToBodyEffect_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  bodyToNeuralFeedback_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  learnedStateTrace_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  recursiveSelfWriteBack_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  generatedNext_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  authorityAndRefusalSettlement_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  noPowerMinting_read_exact := fun receipt => by
    simpa [sourceOwnedResonantDrivenObservationAt] using
      receipt.endpointReadout_true
  occurrenceSourceAt := finiteResonantDrivenSeriesRLCOccurrenceCompile
  occurrenceSource_compiles :=
    finiteResonantDrivenSeriesRLCOccurrenceCompile_involutive
  PersonalLineage := FiniteResonantDrivenSeriesRLCRunFibre source
  lineageOf := id

theorem everyResonantDrivenCoreSource_generatesSourceOwnedCrown
    (source : ResonantDrivenCoreSource) :
    SourceGeneratedTruthChildNeuralBodyCouplingLaw.SourceGeneratedTruthChildNeuralBodyCouplingCrownAt
      (sourceOwnedFiniteResonantDrivenSeriesRLCCouplingLaw source) :=
  (sourceOwnedFiniteResonantDrivenSeriesRLCCouplingLaw source
    ).sourceGeneratedTruthChildNeuralBodyCouplingCrown

def generatedFiniteResonantDrivenSeriesRLCSourceTag
    (source : ResonantDrivenCoreSource) :
    FiniteResonantDrivenSeriesRLCRunOccurrence × Bool :=
  (finiteResonantDrivenSeriesRLCSourceSeed source).val

theorem generatedFiniteResonantDrivenSeriesRLCSourceTag_injective :
    Function.Injective generatedFiniteResonantDrivenSeriesRLCSourceTag := by
  intro left right sameTag
  exact compileFiniteResonantDrivenSeriesRLCRun_injective
    (congrArg Prod.fst sameTag)

theorem generatedFiniteResonantDrivenSeriesRLCOccurrence_preservesExactRun
    (source : ResonantDrivenCoreSource) :
    (finiteResonantDrivenSeriesRLCOccurrenceCompile
      (finiteResonantDrivenSeriesRLCSourceSeed source)).val.1 =
        compileFiniteResonantDrivenSeriesRLCRun source :=
  rfl

theorem sourceOwnedResonantDrivenPresentation_isNonconstant
    (source : ResonantDrivenCoreSource) :
    sourceOwnedResonantDrivenTruthChildView
        (finiteResonantDrivenSeriesRLCSourceSeed source) ≠
      sourceOwnedResonantDrivenTruthChildView
        (finiteResonantDrivenSeriesRLCOccurrenceCompile
          (finiteResonantDrivenSeriesRLCSourceSeed source)) := by
  intro same
  change TruthChildEmpiricalOccurrence.registered =
    TruthChildEmpiricalOccurrence.writebackDeleted at same
  exact (by decide : TruthChildEmpiricalOccurrence.registered ≠
    TruthChildEmpiricalOccurrence.writebackDeleted) same

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.sourceOwnedResonantDrivenObservationAt_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.everyResonantDrivenCoreSource_generatesSourceOwnedCrown
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.generatedFiniteResonantDrivenSeriesRLCSourceTag_injective
