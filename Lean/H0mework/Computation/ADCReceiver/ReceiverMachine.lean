import H0mework.Computation.ADCWire.EnergyWireReceiver

/-!
# Clocked finite-ADC receiver machine

This is a dedicated synchronous register-stage model of the existing finite
ADC receiver.  It captures a packet, parses it, checks calibration, and then
executes the fixed-width energy data path in eight transitions.  All ten
channels advance in parallel and every phase can read only the preceding
phase's payload.  One transition denotes one abstract register clock; this
file does not assert a transistor or gate propagation bound for a physical
sampling-clock period.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface

/-- Signed ADC differences generated in parallel for all ten channels. -/
structure FiniteADCReceiverDifferenceRegisters where
  resistorNumerator : FiniteEmbodimentChannel → BitVec 128
  resistorSpan : FiniteEmbodimentChannel → BitVec 128
  inductorNumerator : FiniteEmbodimentChannel → BitVec 128
  inductorSpan : FiniteEmbodimentChannel → BitVec 128

/-- Squared differences, retaining the signed span words used at readout. -/
structure FiniteADCReceiverSquareRegisters where
  resistorSpan : FiniteEmbodimentChannel → BitVec 128
  inductorSpan : FiniteEmbodimentChannel → BitVec 128
  resistorNumeratorSquared : FiniteEmbodimentChannel → BitVec 128
  resistorSpanSquared : FiniteEmbodimentChannel → BitVec 128
  inductorNumeratorSquared : FiniteEmbodimentChannel → BitVec 128
  inductorSpanSquared : FiniteEmbodimentChannel → BitVec 128

/-- Three independent products generated from the square registers. -/
structure FiniteADCReceiverProductRegisters where
  resistorSpan : FiniteEmbodimentChannel → BitVec 128
  inductorSpan : FiniteEmbodimentChannel → BitVec 128
  thresholdDenominator : FiniteEmbodimentChannel → BitVec 128
  resistorEnergyTerm : FiniteEmbodimentChannel → BitVec 128
  inductorEnergyTerm : FiniteEmbodimentChannel → BitVec 128

/-- The two energy terms have been added but not yet scaled. -/
structure FiniteADCReceiverSumRegisters where
  resistorSpan : FiniteEmbodimentChannel → BitVec 128
  inductorSpan : FiniteEmbodimentChannel → BitVec 128
  thresholdDenominator : FiniteEmbodimentChannel → BitVec 128
  energySum : FiniteEmbodimentChannel → BitVec 128

/-- Final comparator operands after the fixed multiplication by four. -/
structure FiniteADCReceiverScaledRegisters where
  resistorSpan : FiniteEmbodimentChannel → BitVec 128
  inductorSpan : FiniteEmbodimentChannel → BitVec 128
  thresholdDenominator : FiniteEmbodimentChannel → BitVec 128
  scaledEnergyNumerator : FiniteEmbodimentChannel → BitVec 128

/-- Generate the first arithmetic register bank from a calibrated sample. -/
def finiteADCReceiverDifferenceRegisters
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) : FiniteADCReceiverDifferenceRegisters where
  resistorNumerator := fun channel => finiteADCBitVectorDifference128
    (sample.wordsAt .operational .resistor channel)
    (sample.wordsAt .zeroReference .resistor channel)
  resistorSpan := fun channel => finiteADCBitVectorDifference128
    (sample.wordsAt .spanReference .resistor channel)
    (sample.wordsAt .zeroReference .resistor channel)
  inductorNumerator := fun channel => finiteADCBitVectorDifference128
    (sample.wordsAt .operational .inductor channel)
    (sample.wordsAt .zeroReference .inductor channel)
  inductorSpan := fun channel => finiteADCBitVectorDifference128
    (sample.wordsAt .spanReference .inductor channel)
    (sample.wordsAt .zeroReference .inductor channel)

/-- Square all four difference banks in one parallel register phase. -/
def finiteADCReceiverSquareRegisters
    (input : FiniteADCReceiverDifferenceRegisters) : FiniteADCReceiverSquareRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  resistorNumeratorSquared := fun channel =>
    input.resistorNumerator channel * input.resistorNumerator channel
  resistorSpanSquared := fun channel =>
    input.resistorSpan channel * input.resistorSpan channel
  inductorNumeratorSquared := fun channel =>
    input.inductorNumerator channel * input.inductorNumerator channel
  inductorSpanSquared := fun channel =>
    input.inductorSpan channel * input.inductorSpan channel

/-- Generate denominator and two energy products in parallel. -/
def finiteADCReceiverProductRegisters
    (input : FiniteADCReceiverSquareRegisters) : FiniteADCReceiverProductRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  thresholdDenominator := fun channel =>
    input.resistorSpanSquared channel * input.inductorSpanSquared channel
  resistorEnergyTerm := fun channel =>
    input.resistorNumeratorSquared channel * input.inductorSpanSquared channel
  inductorEnergyTerm := fun channel =>
    input.inductorNumeratorSquared channel * input.resistorSpanSquared channel

/-- Add the two energy products in one parallel register phase. -/
def finiteADCReceiverSumRegisters
    (input : FiniteADCReceiverProductRegisters) : FiniteADCReceiverSumRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  thresholdDenominator := input.thresholdDenominator
  energySum := fun channel =>
    input.resistorEnergyTerm channel + input.inductorEnergyTerm channel

/-- Multiply each energy sum by four in one parallel register phase. -/
def finiteADCReceiverScaledRegisters
    (input : FiniteADCReceiverSumRegisters) : FiniteADCReceiverScaledRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  thresholdDenominator := input.thresholdDenominator
  scaledEnergyNumerator := fun channel =>
    BitVec.ofNat 128 4 * input.energySum channel

/-- Read the final registered comparator operands at every channel. -/
def finiteADCReceiverScaledDecision
    (input : FiniteADCReceiverScaledRegisters) : FiniteBinaryDrive :=
  fun channel =>
    (BitVec.zero 128).slt (input.resistorSpan channel) &&
      (BitVec.zero 128).slt (input.inductorSpan channel) &&
      (input.thresholdDenominator channel).ult (input.scaledEnergyNumerator channel)

/-- The nine phases of the dedicated receiver pipeline. -/
inductive FiniteADCReceiverMachinePhase where
  | captured
  | parsed
  | calibrated
  | differenced
  | squared
  | products
  | summed
  | scaled
  | done
  deriving DecidableEq, Repr

/-- Ordinal generated by the linear phase graph. -/
def FiniteADCReceiverMachinePhase.ordinal : FiniteADCReceiverMachinePhase → Nat
  | .captured => 0
  | .parsed => 1
  | .calibrated => 2
  | .differenced => 3
  | .squared => 4
  | .products => 5
  | .summed => 6
  | .scaled => 7
  | .done => 8

/-- Phase-graph distance to the terminal register. -/
def FiniteADCReceiverMachinePhase.ticksToDone
    (phase : FiniteADCReceiverMachinePhase) : Nat :=
  FiniteADCReceiverMachinePhase.done.ordinal - phase.ordinal

/-- A sum type prevents a phase from reading any payload other than its
immediately preceding registered payload.  Rejection propagates as `none` and
therefore has the same phase count as acceptance. -/
inductive FiniteADCReceiverMachineState
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (counterBits : Nat) where
  | captured (lastTick : Nat) (packet : FiniteADCWirePacketAt source counterBits)
  | parsed (sample : Option (FiniteADCDigitalSample source))
  | calibrated (sample : Option (FiniteADCDigitalSample source))
  | differenced (registers : Option FiniteADCReceiverDifferenceRegisters)
  | squared (registers : Option FiniteADCReceiverSquareRegisters)
  | products (registers : Option FiniteADCReceiverProductRegisters)
  | summed (registers : Option FiniteADCReceiverSumRegisters)
  | scaled (registers : Option FiniteADCReceiverScaledRegisters)
  | done (result : Option FiniteBinaryDrive)

/-- Capture a packet without parsing it or precomputing a result. -/
def finiteADCReceiverMachineStart
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) :
    FiniteADCReceiverMachineState source counterBits :=
  .captured lastTick packet

/-- One synchronous transition.  Every branch consumes only its constructor's
payload and writes the next constructor's payload. -/
def finiteADCReceiverMachineStep
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource} {counterBits : Nat} :
    FiniteADCReceiverMachineState source counterBits →
      FiniteADCReceiverMachineState source counterBits
  | .captured lastTick packet => .parsed (parseADCWirePacket source lastTick packet)
  | .parsed none => .calibrated none
  | .parsed (some sample) =>
      if validADCEnergyCalibration sample then .calibrated (some sample) else .calibrated none
  | .calibrated sample => .differenced (sample.map finiteADCReceiverDifferenceRegisters)
  | .differenced registers => .squared (registers.map finiteADCReceiverSquareRegisters)
  | .squared registers => .products (registers.map finiteADCReceiverProductRegisters)
  | .products registers => .summed (registers.map finiteADCReceiverSumRegisters)
  | .summed registers => .scaled (registers.map finiteADCReceiverScaledRegisters)
  | .scaled registers => .done (registers.map finiteADCReceiverScaledDecision)
  | .done result => .done result

/-- The processing count is generated by the captured phase's graph distance. -/
def finiteADCReceiverMachineTicks : Nat :=
  FiniteADCReceiverMachinePhase.captured.ticksToDone

/-- Execute the receiver for the requested number of register clocks. -/
def finiteADCReceiverMachineAfter
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :
    FiniteADCReceiverMachineState source counterBits :=
  (finiteADCReceiverMachineStep^[ticks])
    (finiteADCReceiverMachineStart source lastTick packet)

/-- An outer `none` means unfinished; `some none` is a completed rejection. -/
def finiteADCReceiverMachineOutput
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource} {counterBits : Nat} :
    FiniteADCReceiverMachineState source counterBits → Option (Option FiniteBinaryDrive)
  | .done result => some result
  | _ => none

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
