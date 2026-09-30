import H0mework.Physics.RLCResponse.Transfer

/-!
# Actual sinusoidal particular solution of the driven series-RLC circuit

The phasor response is evaluated as an SI-valued time waveform.  Its voltage
and current derivatives are kernel-checked with respect to physical seconds;
the same waveform then satisfies capacitor, resistor and inductor laws, all
three node KCL equations, and the forced whole-loop KVL equation.

This file constructs the periodic particular solution.  It does not identify
an arbitrary finite-time total response with that periodic solution; a total
response may additionally carry the source-generated homogeneous transient.
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

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Units.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

theorem frequency_voltage_dimension :
    frequencyDimension + voltageDimension =
      voltageDimension - timeDimension := by
  decide

def frequencyTimesVoltage
    (frequency : SIHertz) (voltage : SIVolt) : VoltageRateQuantity :=
  SIQuantity.castDimension frequency_voltage_dimension
    (SIQuantity.mul frequency voltage)

def voltageWaveformDerivativeAt
    (frequency : SIHertz) (phasor : SIVoltagePhasor)
    (physicalTime : SISecond) : VoltageRateQuantity :=
  frequencyTimesVoltage frequency
    ((-Real.sin (frequency.value * physicalTime.value)) • phasor.cosine +
      Real.cos (frequency.value * physicalTime.value) • phasor.sine)

def currentWaveformDerivativeAt
    (frequency : SIHertz) (phasor : SICurrentPhasor)
    (physicalTime : SISecond) : CurrentRateQuantity :=
  frequencyTimesCurrent frequency
    ((-Real.sin (frequency.value * physicalTime.value)) • phasor.cosine +
      Real.cos (frequency.value * physicalTime.value) • phasor.sine)

@[simp] theorem frequencyTimesVoltage_value
    (frequency : SIHertz) (voltage : SIVolt) :
    (frequencyTimesVoltage frequency voltage).value =
      frequency.value * voltage.value := by
  simp [frequencyTimesVoltage]

@[simp] theorem frequencyTimesCurrent_value
    (frequency : SIHertz) (current : SIAmpere) :
    (frequencyTimesCurrent frequency current).value =
      frequency.value * current.value := by
  simp [frequencyTimesCurrent]

@[simp] theorem voltageWaveformDerivativeAt_value
    (frequency : SIHertz) (phasor : SIVoltagePhasor)
    (physicalTime : SISecond) :
    (voltageWaveformDerivativeAt frequency phasor physicalTime).value =
      frequency.value *
        ((-Real.sin (frequency.value * physicalTime.value)) *
            phasor.cosine.value +
          Real.cos (frequency.value * physicalTime.value) *
            phasor.sine.value) := by
  simp [voltageWaveformDerivativeAt]

@[simp] theorem currentWaveformDerivativeAt_value
    (frequency : SIHertz) (phasor : SICurrentPhasor)
    (physicalTime : SISecond) :
    (currentWaveformDerivativeAt frequency phasor physicalTime).value =
      frequency.value *
        ((-Real.sin (frequency.value * physicalTime.value)) *
            phasor.cosine.value +
          Real.cos (frequency.value * physicalTime.value) *
            phasor.sine.value) := by
  simp [currentWaveformDerivativeAt]

theorem voltageWaveform_hasSIQuantityDerivAt
    (frequency : SIHertz) (phasor : SIVoltagePhasor)
    (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (voltageWaveformAt frequency phasor)
      (voltageWaveformDerivativeAt frequency phasor physicalTime)
      physicalTime := by
  constructor
  have phase : HasDerivAt
      (fun time : ℝ => frequency.value * time)
      frequency.value physicalTime.value := by
    simpa using
      (hasDerivAt_id' physicalTime.value).const_mul frequency.value
  have derivative :=
    ((Real.hasDerivAt_cos
        (frequency.value * physicalTime.value)).comp physicalTime.value phase
      ).mul_const phasor.cosine.value |>.add
      (((Real.hasDerivAt_sin
        (frequency.value * physicalTime.value)).comp physicalTime.value phase
      ).mul_const phasor.sine.value)
  convert derivative using 1
  all_goals try rfl
  all_goals simp [voltageWaveformDerivativeAt,
    frequencyTimesVoltage]
  all_goals ring

theorem currentWaveform_hasSIQuantityDerivAt
    (frequency : SIHertz) (phasor : SICurrentPhasor)
    (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (currentWaveformAt frequency phasor)
      (currentWaveformDerivativeAt frequency phasor physicalTime)
      physicalTime := by
  constructor
  have phase : HasDerivAt
      (fun time : ℝ => frequency.value * time)
      frequency.value physicalTime.value := by
    simpa using
      (hasDerivAt_id' physicalTime.value).const_mul frequency.value
  have derivative :=
    ((Real.hasDerivAt_cos
        (frequency.value * physicalTime.value)).comp physicalTime.value phase
      ).mul_const phasor.cosine.value |>.add
      (((Real.hasDerivAt_sin
        (frequency.value * physicalTime.value)).comp physicalTime.value phase
      ).mul_const phasor.sine.value)
  convert derivative using 1
  all_goals try rfl
  all_goals simp [currentWaveformDerivativeAt,
    frequencyTimesCurrent]
  all_goals ring

def drivenPeriodicVoltageResponsePhasorAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) : SIVoltagePhasor :=
  drivenVoltageResponseAt
    (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency drive

def drivenPeriodicCurrentPhasorAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) : SICurrentPhasor :=
  drivenCapacitorCurrentPhasorAt
    (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
    (drivenPeriodicVoltageResponsePhasorAt source channel frequency drive)

def drivenPeriodicVoltageAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) : SIVolt :=
  voltageWaveformAt frequency
    (drivenPeriodicVoltageResponsePhasorAt source channel frequency drive)
    physicalTime

def drivenPeriodicCurrentAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) : SIAmpere :=
  currentWaveformAt frequency
    (drivenPeriodicCurrentPhasorAt source channel frequency drive) physicalTime

theorem drivenPeriodicVoltage_hasSIQuantityDerivAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (drivenPeriodicVoltageAt source channel frequency drive)
      (voltageWaveformDerivativeAt frequency
        (drivenPeriodicVoltageResponsePhasorAt source channel frequency drive)
        physicalTime)
      physicalTime :=
  voltageWaveform_hasSIQuantityDerivAt _ _ _

theorem drivenPeriodicCurrent_hasSIQuantityDerivAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) :
    HasSIQuantityDerivAt
      (drivenPeriodicCurrentAt source channel frequency drive)
      (currentWaveformDerivativeAt frequency
        (drivenPeriodicCurrentPhasorAt source channel frequency drive)
        physicalTime)
      physicalTime :=
  currentWaveform_hasSIQuantityDerivAt _ _ _

theorem drivenPeriodic_capacitorConstitutiveLaw
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) :
    capacitanceTimesVoltageRate
        ((compileFiniteDimensionedSeriesRLCNetlistRun source).capacitanceAt
          channel)
        (voltageWaveformDerivativeAt frequency
          (drivenPeriodicVoltageResponsePhasorAt source channel frequency drive)
          physicalTime) =
      drivenPeriodicCurrentAt source channel frequency drive physicalTime := by
  apply SIQuantity.ext
  simp [drivenPeriodicCurrentAt, drivenPeriodicCurrentPhasorAt,
    drivenCapacitorCurrentPhasorAt, currentWaveformAt,
    voltageWaveformDerivativeAt, frequencyTimesVoltage]
  ring

theorem drivenPeriodic_resistorConstitutiveLaw
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) :
    resistanceTimesCurrent
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).seriesResistanceAt channel)
        (drivenPeriodicCurrentAt source channel frequency drive physicalTime) =
      voltageWaveformAt frequency
        (drivenResistorVoltagePhasorAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
          (drivenPeriodicCurrentPhasorAt source channel frequency drive))
        physicalTime := by
  apply SIQuantity.ext
  simp [drivenPeriodicCurrentAt, drivenResistorVoltagePhasorAt,
    currentWaveformAt, voltageWaveformAt]
  ring

theorem drivenPeriodic_inductorConstitutiveLaw
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond) :
    inductanceTimesCurrentRate
        ((compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt
          channel)
        (currentWaveformDerivativeAt frequency
          (drivenPeriodicCurrentPhasorAt source channel frequency drive)
          physicalTime) =
      voltageWaveformAt frequency
        (drivenInductorVoltagePhasorAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
          (drivenPeriodicCurrentPhasorAt source channel frequency drive))
        physicalTime := by
  apply SIQuantity.ext
  simp [drivenInductorVoltagePhasorAt, currentWaveformDerivativeAt,
    frequencyTimesCurrent, voltageWaveformAt]
  ring

def drivenSeriesRLCElementCurrentAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond)
    (_element : SeriesRLCCoreElementKind) : SIAmpere :=
  drivenPeriodicCurrentAt source channel frequency drive physicalTime

def drivenSeriesRLCNodeCurrentAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond)
    (node : SeriesRLCLocalNode) : SIAmpere :=
  ((seriesRLCCoreIncidence node .seriesResistor : ℝ) •
      drivenSeriesRLCElementCurrentAt source channel frequency drive
        physicalTime .seriesResistor) +
    ((seriesRLCCoreIncidence node .inductor : ℝ) •
      drivenSeriesRLCElementCurrentAt source channel frequency drive
        physicalTime .inductor) +
    ((seriesRLCCoreIncidence node .capacitor : ℝ) •
      drivenSeriesRLCElementCurrentAt source channel frequency drive
        physicalTime .capacitor)

theorem drivenPeriodic_kirchhoffCurrentLaw
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (physicalTime : SISecond)
    (node : SeriesRLCLocalNode) :
    drivenSeriesRLCNodeCurrentAt source channel frequency drive physicalTime
      node = 0 := by
  apply SIQuantity.ext
  cases node <;>
    simp [drivenSeriesRLCNodeCurrentAt, drivenSeriesRLCElementCurrentAt,
      seriesRLCCoreIncidence]

theorem drivenPeriodic_responsePhasor_componentKVL
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) (drive : SIVoltagePhasor) :
    drive =
      drivenPeriodicVoltageResponsePhasorAt source channel frequency drive +
        drivenResistorVoltagePhasorAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel
          (drivenPeriodicCurrentPhasorAt source channel frequency drive) +
        drivenInductorVoltagePhasorAt
          (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
          (drivenPeriodicCurrentPhasorAt source channel frequency drive) := by
  calc
    drive = drivenVoltageCommandForAt
        (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
        (drivenPeriodicVoltageResponsePhasorAt source channel frequency drive) :=
      (drivenVoltageCommand_response_eq source channel frequency
        frequencyPositive drive).symm
    _ = _ := drivenVoltageCommandFor_eq_componentKVL _ _ _ _

theorem drivenPeriodic_forcedKirchhoffVoltageLaw
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (frequencyPositive : 0 < frequency.value) (drive : SIVoltagePhasor)
    (physicalTime : SISecond) :
    inductanceTimesCurrentRate
        ((compileFiniteDimensionedSeriesRLCNetlistRun source).inductanceAt
          channel)
        (currentWaveformDerivativeAt frequency
          (drivenPeriodicCurrentPhasorAt source channel frequency drive)
          physicalTime) +
      resistanceTimesCurrent
        ((compileFiniteDimensionedSeriesRLCNetlistRun source
          ).seriesResistanceAt channel)
        (drivenPeriodicCurrentAt source channel frequency drive physicalTime) +
      drivenPeriodicVoltageAt source channel frequency drive physicalTime =
        voltageWaveformAt frequency drive physicalTime := by
  rw [drivenPeriodic_inductorConstitutiveLaw,
    drivenPeriodic_resistorConstitutiveLaw]
  have phasorKVL := drivenPeriodic_responsePhasor_componentKVL
    source channel frequency frequencyPositive drive
  have waveformKVL := congrArg
    (fun phasor => (voltageWaveformAt frequency phasor physicalTime).value)
    phasorKVL
  apply SIQuantity.ext
  simp only [SIQuantity.add_value, drivenPeriodicVoltageAt,
    voltageWaveformAt_value, voltagePhasor_add_cosine,
    voltagePhasor_add_sine] at waveformKVL ⊢
  linear_combination waveformKVL.symm

structure SourceGeneratedDrivenPeriodicParticularAt
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) : Prop where
  frequencyPositive : 0 < frequency.value
  responseIsForwardTransfer :
    drivenVoltageCommandForAt
      (compileFiniteDimensionedSeriesRLCNetlistRun source) channel frequency
      (drivenPeriodicVoltageResponsePhasorAt source channel frequency drive) =
        drive
  voltageDerivative : ∀ physicalTime,
    type_of% (drivenPeriodicVoltage_hasSIQuantityDerivAt
      source channel frequency drive physicalTime)
  currentDerivative : ∀ physicalTime,
    type_of% (drivenPeriodicCurrent_hasSIQuantityDerivAt
      source channel frequency drive physicalTime)
  capacitorLaw : ∀ physicalTime,
    type_of% (drivenPeriodic_capacitorConstitutiveLaw
      source channel frequency drive physicalTime)
  resistorLaw : ∀ physicalTime,
    type_of% (drivenPeriodic_resistorConstitutiveLaw
      source channel frequency drive physicalTime)
  inductorLaw : ∀ physicalTime,
    type_of% (drivenPeriodic_inductorConstitutiveLaw
      source channel frequency drive physicalTime)
  kirchhoffCurrent : ∀ physicalTime node,
    type_of% (drivenPeriodic_kirchhoffCurrentLaw
      source channel frequency drive physicalTime node)
  forcedKirchhoffVoltage : ∀ physicalTime,
    type_of% (drivenPeriodic_forcedKirchhoffVoltageLaw
      source channel frequency frequencyPositive drive physicalTime)

theorem sourceGeneratedDrivenPeriodicParticular
    (source : DimensionedSeriesRLCSource)
    (channel : FiniteEmbodimentChannel) (frequency : SIHertz)
    (drive : SIVoltagePhasor) (frequencyPositive : 0 < frequency.value) :
    SourceGeneratedDrivenPeriodicParticularAt
      source channel frequency drive where
  frequencyPositive := frequencyPositive
  responseIsForwardTransfer :=
    drivenVoltageCommand_response_eq source channel frequency
      frequencyPositive drive
  voltageDerivative := drivenPeriodicVoltage_hasSIQuantityDerivAt
    source channel frequency drive
  currentDerivative := drivenPeriodicCurrent_hasSIQuantityDerivAt
    source channel frequency drive
  capacitorLaw := drivenPeriodic_capacitorConstitutiveLaw
    source channel frequency drive
  resistorLaw := drivenPeriodic_resistorConstitutiveLaw
    source channel frequency drive
  inductorLaw := drivenPeriodic_inductorConstitutiveLaw
    source channel frequency drive
  kirchhoffCurrent := drivenPeriodic_kirchhoffCurrentLaw
    source channel frequency drive
  forcedKirchhoffVoltage := drivenPeriodic_forcedKirchhoffVoltageLaw
    source channel frequency frequencyPositive drive

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

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical.Netlist.Dissipative.Dimensioned.Driven.Producer.sourceGeneratedDrivenPeriodicParticular
