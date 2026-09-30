import H0mework.Computation.ADCGates.Gate128Correctness
import H0mework.Computation.ADCReceiver.ReceiverMachineCorrectness

/-!
# Finite gate graphs execute the receiver's arithmetic stages

The existing phase carrier and packet/calibration admission are unchanged.
Every 128-bit subtraction, multiplication, addition and ordered comparison
below reads a compiled gate graph. No specification BitVec arithmetic is used
as a substitute execution result.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Physical.Interface

def finiteADCGateDifferenceRegisters
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    (sample : FiniteADCDigitalSample source) : FiniteADCReceiverDifferenceRegisters where
  resistorNumerator := fun channel => finiteADC128GateSub
    (BitVec.ofInt 128 (sample.wordsAt .operational .resistor channel).val)
    (BitVec.ofInt 128 (sample.wordsAt .zeroReference .resistor channel).val)
  resistorSpan := fun channel => finiteADC128GateSub
    (BitVec.ofInt 128 (sample.wordsAt .spanReference .resistor channel).val)
    (BitVec.ofInt 128 (sample.wordsAt .zeroReference .resistor channel).val)
  inductorNumerator := fun channel => finiteADC128GateSub
    (BitVec.ofInt 128 (sample.wordsAt .operational .inductor channel).val)
    (BitVec.ofInt 128 (sample.wordsAt .zeroReference .inductor channel).val)
  inductorSpan := fun channel => finiteADC128GateSub
    (BitVec.ofInt 128 (sample.wordsAt .spanReference .inductor channel).val)
    (BitVec.ofInt 128 (sample.wordsAt .zeroReference .inductor channel).val)

def finiteADCGateSquareRegisters
    (input : FiniteADCReceiverDifferenceRegisters) : FiniteADCReceiverSquareRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  resistorNumeratorSquared := fun channel =>
    finiteADC128GateMul (input.resistorNumerator channel) (input.resistorNumerator channel)
  resistorSpanSquared := fun channel =>
    finiteADC128GateMul (input.resistorSpan channel) (input.resistorSpan channel)
  inductorNumeratorSquared := fun channel =>
    finiteADC128GateMul (input.inductorNumerator channel) (input.inductorNumerator channel)
  inductorSpanSquared := fun channel =>
    finiteADC128GateMul (input.inductorSpan channel) (input.inductorSpan channel)

def finiteADCGateProductRegisters
    (input : FiniteADCReceiverSquareRegisters) : FiniteADCReceiverProductRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  thresholdDenominator := fun channel =>
    finiteADC128GateMul (input.resistorSpanSquared channel) (input.inductorSpanSquared channel)
  resistorEnergyTerm := fun channel =>
    finiteADC128GateMul (input.resistorNumeratorSquared channel) (input.inductorSpanSquared channel)
  inductorEnergyTerm := fun channel =>
    finiteADC128GateMul (input.inductorNumeratorSquared channel) (input.resistorSpanSquared channel)

def finiteADCGateSumRegisters
    (input : FiniteADCReceiverProductRegisters) : FiniteADCReceiverSumRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  thresholdDenominator := input.thresholdDenominator
  energySum := fun channel =>
    finiteADC128GateAdd (input.resistorEnergyTerm channel) (input.inductorEnergyTerm channel)

def finiteADCGateScaledRegisters
    (input : FiniteADCReceiverSumRegisters) : FiniteADCReceiverScaledRegisters where
  resistorSpan := input.resistorSpan
  inductorSpan := input.inductorSpan
  thresholdDenominator := input.thresholdDenominator
  scaledEnergyNumerator := fun channel =>
    finiteADC128GateMul (BitVec.ofNat 128 4) (input.energySum channel)

def finiteADCGateScaledDecision
    (input : FiniteADCReceiverScaledRegisters) : FiniteBinaryDrive :=
  fun channel =>
    finiteADC128GateSLt (BitVec.zero 128) (input.resistorSpan channel) &&
      finiteADC128GateSLt (BitVec.zero 128) (input.inductorSpan channel) &&
      finiteADC128GateULt (input.thresholdDenominator channel) (input.scaledEnergyNumerator channel)

/-- Only the arithmetic realization changes; the same phase and failure
constructors retain the original packet and calibration semantics. -/
def finiteADCGateReceiverMachineStep
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource} {counterBits : Nat} :
    FiniteADCReceiverMachineState source counterBits →
      FiniteADCReceiverMachineState source counterBits
  | .captured lastTick packet => .parsed (parseADCWirePacket source lastTick packet)
  | .parsed none => .calibrated none
  | .parsed (some sample) =>
      if validADCEnergyCalibration sample then .calibrated (some sample) else .calibrated none
  | .calibrated sample => .differenced (sample.map finiteADCGateDifferenceRegisters)
  | .differenced registers => .squared (registers.map finiteADCGateSquareRegisters)
  | .squared registers => .products (registers.map finiteADCGateProductRegisters)
  | .products registers => .summed (registers.map finiteADCGateSumRegisters)
  | .summed registers => .scaled (registers.map finiteADCGateScaledRegisters)
  | .scaled registers => .done (registers.map finiteADCGateScaledDecision)
  | .done result => .done result

def finiteADCGateReceiverMachineAfter
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :
    FiniteADCReceiverMachineState source counterBits :=
  (finiteADCGateReceiverMachineStep^[ticks])
    (finiteADCReceiverMachineStart source lastTick packet)

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
