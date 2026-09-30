import H0mework.Physics.Measurement.Voltage
import H0mework.Physics.ADCSource.OwnedResonantCoupling

/-!
# Source-generated noisy, metered synchronous sample

A physical RLC fixture, finite half-power-band interference code, and finite
affine meter code compile an actual three-frame voltage table.  The operational
row contains the total-response resistor/inductor voltage plus generated
physical interference; the other rows are zero and span references from the
same meter.

The decoder reads only those raw rows.  Exact two-point calibration removes
the generated affine gain/offset, after which synchronous demodulation leaves
the actual transient plus the finite-band interference.  The compiler chooses
the transient duration from the remaining margin `1/8 - noiseBudget`, so the
combined endpoint disturbance is strictly below `1/8`.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface

noncomputable section

@[ext] structure FiniteNoisyMeteredSynchronousFixtureSource where
  fixture : ResonantDrivenSynchronousFixtureSource
  noiseCode : FiniteHalfPowerBandNoiseCode
  meterCode : FiniteAffineMeterCode

def finiteNoisyMeteredTransientTolerance
    (source : FiniteNoisyMeteredSynchronousFixtureSource) : ℝ :=
  (1 : ℝ) / 8 - finiteHalfPowerBandNoiseBudget source.noiseCode

theorem finiteNoisyMeteredTransientTolerance_pos
    (source : FiniteNoisyMeteredSynchronousFixtureSource) :
    0 < finiteNoisyMeteredTransientTolerance source := by
  unfold finiteNoisyMeteredTransientTolerance
  have noise := finiteHalfPowerBandNoiseBudget_lt_sixteenth source.noiseCode
  linarith

def finiteNoisyMeteredSynchronousDuration
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) : SISecond :=
  resonantSynchronousSettlingDurationFor
    (finiteNoisyMeteredTransientTolerance source)
    source.fixture.coreSource input source.fixture.initial

theorem finiteNoisyMeteredSynchronousDuration_pos
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    0 < (finiteNoisyMeteredSynchronousDuration source input).value :=
  resonantSynchronousSettlingDurationFor_pos
    (finiteNoisyMeteredTransientTolerance source)
    (finiteNoisyMeteredTransientTolerance_pos source)
    source.fixture.coreSource input source.fixture.initial

def finiteNoisyMeteredActualSenseVoltageAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIVolt :=
  match leg with
  | .resistor => resonantActualResistorVoltageAt
      source.fixture.coreSource input source.fixture.initial channel physicalTime
  | .inductor => resonantActualInductorVoltageAt
      source.fixture.coreSource input source.fixture.initial channel physicalTime

def finiteNoisyMeteredPhysicalNoiseAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIVolt :=
  finiteHalfPowerBandNoiseAt source.noiseCode leg
      source.fixture.coreSource channel physicalTime •
    finiteAffineMeterSenseScaleAt
      source.fixture.coreSource leg channel

def finiteNoisyMeteredOperationalVoltageAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel)
    (physicalTime : SISecond) : SIVolt :=
  finiteNoisyMeteredActualSenseVoltageAt
      source input leg channel physicalTime +
    finiteNoisyMeteredPhysicalNoiseAt source leg channel physicalTime

def finiteNoisyMeteredRawVoltageAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState)
    (physicalTime : SISecond)
    (frame : FiniteAffineMeterFrame)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : SIVolt :=
  match frame with
  | .zeroReference => finiteAffineMeterZeroReferenceAt
      source.meterCode source.fixture.coreSource leg channel
  | .spanReference => finiteAffineMeterSpanReferenceAt
      source.meterCode source.fixture.coreSource leg channel
  | .operational => finiteAffineMeterRawAt
      source.meterCode source.fixture.coreSource leg channel
      (finiteNoisyMeteredOperationalVoltageAt
        source input leg channel physicalTime)

/-- Pure compiled sample data.  It contains the actual input rows and raw
voltage table, but no decoded state, error proof, tolerance, verdict, receipt,
or crown. -/
@[ext] structure FiniteNoisyMeteredSynchronousSampleOccurrence where
  drivenRun : FiniteResonantDrivenSeriesRLCRunOccurrence
  driveState : FiniteEmbodimentState
  initial : FiniteDimensionedSeriesRLCPortState
  noiseCode : FiniteHalfPowerBandNoiseCode
  meterCode : FiniteAffineMeterCode
  executedDuration : SISecond
  rawVoltageAt : FiniteAffineMeterFrame → SynchronousSenseLeg →
    FiniteEmbodimentChannel → SIVolt

def compileFiniteNoisyMeteredSynchronousSample
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    FiniteNoisyMeteredSynchronousSampleOccurrence where
  drivenRun := compileFiniteResonantDrivenSeriesRLCRun
    source.fixture.coreSource
  driveState := input
  initial := source.fixture.initial
  noiseCode := source.noiseCode
  meterCode := source.meterCode
  executedDuration := finiteNoisyMeteredSynchronousDuration source input
  rawVoltageAt := finiteNoisyMeteredRawVoltageAt source input
    (finiteNoisyMeteredSynchronousDuration source input)

def compileFiniteNoisyMeteredSynchronousRequest :
    FiniteNoisyMeteredSynchronousFixtureSource × FiniteEmbodimentState →
      FiniteNoisyMeteredSynchronousSampleOccurrence :=
  fun request => compileFiniteNoisyMeteredSynchronousSample request.1 request.2

theorem compileFiniteNoisyMeteredSynchronousRequest_injective :
    Function.Injective compileFiniteNoisyMeteredSynchronousRequest := by
  rintro ⟨leftSource, leftInput⟩ ⟨rightSource, rightInput⟩ sameRun
  apply Prod.ext
  · apply FiniteNoisyMeteredSynchronousFixtureSource.ext
    · apply ResonantDrivenSynchronousFixtureSource.ext
      · apply compileFiniteResonantDrivenSeriesRLCRun_injective
        exact congrArg FiniteNoisyMeteredSynchronousSampleOccurrence.drivenRun
          sameRun
      · exact congrArg FiniteNoisyMeteredSynchronousSampleOccurrence.initial
          sameRun
    · exact congrArg FiniteNoisyMeteredSynchronousSampleOccurrence.noiseCode
        sameRun
    · exact congrArg FiniteNoisyMeteredSynchronousSampleOccurrence.meterCode
        sameRun
  · exact congrArg FiniteNoisyMeteredSynchronousSampleOccurrence.driveState
      sameRun

def finiteNoisyMeteredDecodedLegAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (run : FiniteNoisyMeteredSynchronousSampleOccurrence)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) : ℝ :=
  decodedFiniteAffineMeterNormalizedRead
    (run.rawVoltageAt .zeroReference leg channel)
    (run.rawVoltageAt .spanReference leg channel)
    (run.rawVoltageAt .operational leg channel)
    (finiteAffineMeterSenseScaleAt source.fixture.coreSource leg channel)

def finiteNoisyMeteredDecodedStateAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (run : FiniteNoisyMeteredSynchronousSampleOccurrence) :
    FiniteEmbodimentState :=
  fun channel => synchronousDemodulatedPortAt
    (resonantSynchronousPhaseAt source.fixture.coreSource channel
      run.executedDuration)
    (finiteNoisyMeteredDecodedLegAt source run .resistor channel)
    (finiteNoisyMeteredDecodedLegAt source run .inductor channel)

def finiteNoisyMeteredDecodedHilbertOutputAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (run : FiniteNoisyMeteredSynchronousSampleOccurrence) :
    HilbertEmbodimentState :=
  encodeHilbert (finiteNoisyMeteredDecodedStateAt source run)

theorem compiledFiniteNoisyMeteredDecodedLeg_eq
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState)
    (leg : SynchronousSenseLeg)
    (channel : FiniteEmbodimentChannel) :
    finiteNoisyMeteredDecodedLegAt source
        (compileFiniteNoisyMeteredSynchronousSample source input) leg channel =
      (finiteNoisyMeteredOperationalVoltageAt source input leg channel
          (finiteNoisyMeteredSynchronousDuration source input)).value /
        (finiteAffineMeterSenseScaleAt
          source.fixture.coreSource leg channel).value := by
  unfold finiteNoisyMeteredDecodedLegAt
    compileFiniteNoisyMeteredSynchronousSample finiteNoisyMeteredRawVoltageAt
  exact decodedFiniteAffineMeterNormalizedRead_eq_physical
    source.meterCode source.fixture.coreSource leg channel _

theorem compiledFiniteNoisyMeteredDecodedResistor_eq
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    finiteNoisyMeteredDecodedLegAt source
        (compileFiniteNoisyMeteredSynchronousSample source input)
        .resistor channel =
      resonantActualNormalizedResistorAt source.fixture.coreSource input
          source.fixture.initial channel
          (finiteNoisyMeteredSynchronousDuration source input) +
        finiteHalfPowerBandNoiseAt source.noiseCode .resistor
          source.fixture.coreSource channel
          (finiteNoisyMeteredSynchronousDuration source input) := by
  rw [compiledFiniteNoisyMeteredDecodedLeg_eq]
  unfold finiteNoisyMeteredOperationalVoltageAt
    finiteNoisyMeteredActualSenseVoltageAt
    finiteNoisyMeteredPhysicalNoiseAt
    finiteAffineMeterSenseScaleAt resonantActualNormalizedResistorAt
  simp only [SIQuantity.add_value, SIQuantity.smul_value]
  field_simp [source.fixture.coreSource.2.voltageScale_ne]

theorem compiledFiniteNoisyMeteredDecodedInductor_eq
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState)
    (channel : FiniteEmbodimentChannel) :
    finiteNoisyMeteredDecodedLegAt source
        (compileFiniteNoisyMeteredSynchronousSample source input)
        .inductor channel =
      resonantActualNormalizedInductorAt source.fixture.coreSource input
          source.fixture.initial channel
          (finiteNoisyMeteredSynchronousDuration source input) +
        finiteHalfPowerBandNoiseAt source.noiseCode .inductor
          source.fixture.coreSource channel
          (finiteNoisyMeteredSynchronousDuration source input) := by
  rw [compiledFiniteNoisyMeteredDecodedLeg_eq]
  unfold finiteNoisyMeteredOperationalVoltageAt
    finiteNoisyMeteredActualSenseVoltageAt
    finiteNoisyMeteredPhysicalNoiseAt
    finiteAffineMeterSenseScaleAt resonantActualNormalizedInductorAt
  simp only [SIQuantity.add_value, SIQuantity.smul_value]
  field_simp [ne_of_gt (resonantInductorOutputScale_pos
    (resonantDrivenCoreDimensionedSource source.fixture.coreSource) channel)]

theorem compiledFiniteNoisyMeteredDecodedState_eq_actual_add_noise
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    finiteNoisyMeteredDecodedStateAt source
        (compileFiniteNoisyMeteredSynchronousSample source input) =
      resonantActualSynchronousStateAt source.fixture.coreSource input
          source.fixture.initial
          (finiteNoisyMeteredSynchronousDuration source input) +
        finiteHalfPowerBandSynchronousNoiseStateAt source.noiseCode
          source.fixture.coreSource
          (finiteNoisyMeteredSynchronousDuration source input) := by
  funext channel
  rw [finiteNoisyMeteredDecodedStateAt,
    compiledFiniteNoisyMeteredDecodedResistor_eq,
    compiledFiniteNoisyMeteredDecodedInductor_eq]
  simp only [compileFiniteNoisyMeteredSynchronousSample]
  unfold resonantActualSynchronousStateAt
    finiteHalfPowerBandSynchronousNoiseStateAt
    synchronousDemodulatedPortAt
  apply Prod.ext <;> dsimp <;> ring

theorem compiledFiniteNoisyMeteredHilbertError_eq
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    finiteNoisyMeteredDecodedHilbertOutputAt source
        (compileFiniteNoisyMeteredSynchronousSample source input) -
      idealQuarterOperator (encodeHilbert input) =
    (resonantActualSynchronousHilbertOutputAt source.fixture.coreSource input
          source.fixture.initial
          (finiteNoisyMeteredSynchronousDuration source input) -
        idealQuarterOperator (encodeHilbert input)) +
      finiteHalfPowerBandSynchronousHilbertNoiseAt source.noiseCode
        source.fixture.coreSource
        (finiteNoisyMeteredSynchronousDuration source input) := by
  rw [finiteNoisyMeteredDecodedHilbertOutputAt,
    compiledFiniteNoisyMeteredDecodedState_eq_actual_add_noise]
  rw [← complexHilbertPortEquiv_apply,
    map_add, complexHilbertPortEquiv_apply, complexHilbertPortEquiv_apply]
  unfold resonantActualSynchronousHilbertOutputAt
    finiteHalfPowerBandSynchronousHilbertNoiseAt
  abel

theorem compiledFiniteNoisyMeteredHilbertError_lt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    ‖finiteNoisyMeteredDecodedHilbertOutputAt source
          (compileFiniteNoisyMeteredSynchronousSample source input) -
        idealQuarterOperator (encodeHilbert input)‖ < (1 : ℝ) / 8 := by
  rw [compiledFiniteNoisyMeteredHilbertError_eq]
  have transient := resonantSynchronous_afterGeneratedDurationFor_error_lt
    (finiteNoisyMeteredTransientTolerance source)
    (finiteNoisyMeteredTransientTolerance_pos source)
    source.fixture.coreSource input source.fixture.initial
    (finiteNoisyMeteredSynchronousDuration source input) le_rfl
  have noise := finiteHalfPowerBandSynchronousHilbertNoise_norm_le_budget
    source.noiseCode source.fixture.coreSource
    (finiteNoisyMeteredSynchronousDuration source input)
  exact lt_of_le_of_lt (norm_add_le _ _) (by
    unfold finiteNoisyMeteredTransientTolerance at transient
    linarith)

def finiteNoisyMeteredSynchronousDisturbance
    (source : FiniteNoisyMeteredSynchronousFixtureSource) :
    EndpointDisturbance :=
  fun input => finiteNoisyMeteredDecodedHilbertOutputAt source
      (compileFiniteNoisyMeteredSynchronousSample source input) -
    idealQuarterOperator (encodeHilbert input)

theorem finiteNoisyMeteredSynchronous_hasAdditiveTolerance
    (source : FiniteNoisyMeteredSynchronousFixtureSource) :
    AdditiveDisturbanceToleranceAt idealQuarterOperator
      (finiteNoisyMeteredSynchronousDisturbance source) where
  linearPartTolerance := by norm_num
  disturbanceBound := compiledFiniteNoisyMeteredHilbertError_lt source

theorem compiledFiniteNoisyMeteredState_eq_disturbed
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    finiteNoisyMeteredDecodedStateAt source
        (compileFiniteNoisyMeteredSynchronousSample source input) =
      disturbedImplementedState idealQuarterOperator
        (finiteNoisyMeteredSynchronousDisturbance source) input := by
  apply complexHilbertPortEquiv.injective
  rw [complexHilbertPortEquiv_apply, complexHilbertPortEquiv_apply,
    encodeHilbert_disturbedImplementedState]
  unfold finiteNoisyMeteredSynchronousDisturbance
    finiteNoisyMeteredDecodedHilbertOutputAt
  abel

structure SourceGeneratedFiniteNoisyMeteredSynchronousSampleAt
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) : Prop where
  requestCompilerInjective :
    Function.Injective compileFiniteNoisyMeteredSynchronousRequest
  totalResponse : SourceGeneratedDrivenTotalResponseAt
    (resonantDrivenCoreDimensionedSource source.fixture.coreSource)
    (sourceOwnedResonantDrivenFrequencyAt source.fixture.coreSource)
    (sourceOwnedResonantDrivenDriveAt source.fixture.coreSource input)
    source.fixture.initial
  halfPowerBand : ∀ channel,
    SourceGeneratedExactHalfPowerBandwidthAt
      (resonantDrivenCoreDimensionedSource source.fixture.coreSource) channel
  noiseBudgetPositiveMargin :
    finiteHalfPowerBandNoiseBudget source.noiseCode < (1 : ℝ) / 16
  metrology : ∀ leg channel,
    SourceGeneratedFiniteAffineVoltageMetrologyAt
      source.meterCode source.fixture.coreSource leg channel
  executedDurationPositive :
    0 < (compileFiniteNoisyMeteredSynchronousSample
      source input).executedDuration.value
  calibratedOperationalExact : ∀ leg channel,
    type_of% (compiledFiniteNoisyMeteredDecodedLeg_eq
      source input leg channel)
  endpointHilbertError :
    ‖finiteNoisyMeteredDecodedHilbertOutputAt source
          (compileFiniteNoisyMeteredSynchronousSample source input) -
        idealQuarterOperator (encodeHilbert input)‖ < (1 : ℝ) / 8
  endpointCommutes :
    finiteNoisyMeteredDecodedStateAt source
        (compileFiniteNoisyMeteredSynchronousSample source input) =
      disturbedImplementedState idealQuarterOperator
        (finiteNoisyMeteredSynchronousDisturbance source) input

theorem sourceGeneratedFiniteNoisyMeteredSynchronousSample
    (source : FiniteNoisyMeteredSynchronousFixtureSource)
    (input : FiniteEmbodimentState) :
    SourceGeneratedFiniteNoisyMeteredSynchronousSampleAt source input where
  requestCompilerInjective :=
    compileFiniteNoisyMeteredSynchronousRequest_injective
  totalResponse := everyResonantDrivenCoreSource_generatesTotalResponse
    source.fixture.coreSource input source.fixture.initial
  halfPowerBand := sourceGeneratedExactHalfPowerBandwidth
    (resonantDrivenCoreDimensionedSource source.fixture.coreSource)
  noiseBudgetPositiveMargin :=
    finiteHalfPowerBandNoiseBudget_lt_sixteenth source.noiseCode
  metrology := sourceGeneratedFiniteAffineVoltageMetrology
    source.meterCode source.fixture.coreSource
  executedDurationPositive :=
    finiteNoisyMeteredSynchronousDuration_pos source input
  calibratedOperationalExact := compiledFiniteNoisyMeteredDecodedLeg_eq
    source input
  endpointHilbertError := compiledFiniteNoisyMeteredHilbertError_lt
    source input
  endpointCommutes := compiledFiniteNoisyMeteredState_eq_disturbed
    source input

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.compileFiniteNoisyMeteredSynchronousRequest_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.sourceGeneratedFiniteNoisyMeteredSynchronousSample
