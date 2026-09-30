import H0mework.Computation.ADCGates.RawAdmissionGateCorrectness
import H0mework.Computation.ADCGates.GateReceiverMachineCorrectness

/-!
# Source-owned raw-byte receiver phases

Before arithmetic, the machine retains the actual packet rather than decoding
signed integers and later packing them again. Its range witness is emitted by
the actual packet gate branch. Decoding appears only in the logical readout;
runtime differences read raw finite words directly.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

/-- A local code-indexed gate-generated range guard, not a promised final receiver result. -/
structure FiniteADCRangeCheckedRawPacketFor
    (code : FiniteADCResolutionCode)
    (counterBits lastTick : Nat) where
  packet : FiniteADCWirePacketFor code counterBits
  gateTrue : finiteADCRawPacketGateRunFor code lastTick packet = true

/-- The physical receiver uses the same code-indexed carrier at its source ADC coordinate. -/
abbrev FiniteADCRangeCheckedRawPacket
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (counterBits lastTick : Nat) :=
  FiniteADCRangeCheckedRawPacketFor source.adcCode counterBits lastTick

theorem FiniteADCRangeCheckedRawPacketFor.validRaw
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    validADCWirePacketFor code lastTick checked.packet := by
  have accepted := checked.gateTrue
  rw [finiteADCRawPacketGateFor_exact] at accepted
  exact of_decide_eq_true accepted

theorem FiniteADCRangeCheckedRawPacketFor.validWords
    {code : FiniteADCResolutionCode} {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    ∀ frame leg channel, validADCWord code (checked.packet.2 frame leg channel) :=
  checked.validRaw.2

/-- Source-facing validity recovered from the code-indexed carrier at that
source's installed ADC coordinate. -/
theorem FiniteADCRangeCheckedRawPacketFor.valid
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacket source counterBits lastTick) :
    validADCWirePacket source lastTick checked.packet :=
  checked.validRaw

theorem FiniteADCRangeCheckedRawPacket.valid
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacket source counterBits lastTick) :
    validADCWirePacket source lastTick checked.packet :=
  checked.validRaw

def finiteADCRawDifferenceRegistersFor
    {code : FiniteADCResolutionCode}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacketFor code counterBits lastTick) :
    FiniteADCReceiverDifferenceRegisters where
  resistorNumerator := fun channel => finiteADC128GateSub
    (BitVec.ofNat 128 (checked.packet.2 .operational .resistor channel).val)
    (BitVec.ofNat 128 (checked.packet.2 .zeroReference .resistor channel).val)
  resistorSpan := fun channel => finiteADC128GateSub
    (BitVec.ofNat 128 (checked.packet.2 .spanReference .resistor channel).val)
    (BitVec.ofNat 128 (checked.packet.2 .zeroReference .resistor channel).val)
  inductorNumerator := fun channel => finiteADC128GateSub
    (BitVec.ofNat 128 (checked.packet.2 .operational .inductor channel).val)
    (BitVec.ofNat 128 (checked.packet.2 .zeroReference .inductor channel).val)
  inductorSpan := fun channel => finiteADC128GateSub
    (BitVec.ofNat 128 (checked.packet.2 .spanReference .inductor channel).val)
    (BitVec.ofNat 128 (checked.packet.2 .zeroReference .inductor channel).val)

/-- Legacy physical-source projection of the code-only raw subtraction primitive. -/
def finiteADCRawDifferenceRegisters
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat}
    (checked : FiniteADCRangeCheckedRawPacket source counterBits lastTick) :
    FiniteADCReceiverDifferenceRegisters :=
  finiteADCRawDifferenceRegistersFor checked

inductive FiniteADCRawReceiverState
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    (counterBits lastTick : Nat) where
  | captured (packet : FiniteADCWirePacketAt source counterBits)
  | parsed (packet : Option (FiniteADCRangeCheckedRawPacket source counterBits lastTick))
  | calibrated (packet : Option (FiniteADCRangeCheckedRawPacket source counterBits lastTick))
  | differenced (registers : Option FiniteADCReceiverDifferenceRegisters)
  | squared (registers : Option FiniteADCReceiverSquareRegisters)
  | products (registers : Option FiniteADCReceiverProductRegisters)
  | summed (registers : Option FiniteADCReceiverSumRegisters)
  | scaled (registers : Option FiniteADCReceiverScaledRegisters)
  | done (result : Option FiniteBinaryDrive)

def finiteADCRawReceiverStep
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat} :
    FiniteADCRawReceiverState source counterBits lastTick →
      FiniteADCRawReceiverState source counterBits lastTick
  | .captured packet =>
      if accepted : finiteADCRawPacketGateRun source lastTick packet = true then
        .parsed (some ⟨packet, accepted⟩)
      else .parsed none
  | .parsed none => .calibrated none
  | .parsed (some checked) =>
      if finiteADCRawCalibrationGateRun source lastTick checked.packet = true then
        .calibrated (some checked)
      else .calibrated none
  | .calibrated packet => .differenced (packet.map finiteADCRawDifferenceRegisters)
  | .differenced registers => .squared (registers.map finiteADCGateSquareRegisters)
  | .squared registers => .products (registers.map finiteADCGateProductRegisters)
  | .products registers => .summed (registers.map finiteADCGateSumRegisters)
  | .summed registers => .scaled (registers.map finiteADCGateScaledRegisters)
  | .scaled registers => .done (registers.map finiteADCGateScaledDecision)
  | .done result => .done result

def finiteADCRawReceiverAfter
    (source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource)
    {counterBits : Nat} (lastTick : Nat)
    (packet : FiniteADCWirePacketAt source counterBits) (ticks : Nat) :
    FiniteADCRawReceiverState source counterBits lastTick :=
  (finiteADCRawReceiverStep^[ticks]) (.captured packet)

/-- Proof-side restriction to the old signed-symbol state. The raw runtime
and its output function never call this decoder-bearing readout. -/
def finiteADCRawReceiverReadout
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat} :
    FiniteADCRawReceiverState source counterBits lastTick →
      FiniteADCReceiverMachineState source counterBits
  | .captured packet => .captured lastTick packet
  | .parsed packet => .parsed (packet.map fun checked => unpackADCWirePacket source checked.packet)
  | .calibrated packet =>
      .calibrated (packet.map fun checked => unpackADCWirePacket source checked.packet)
  | .differenced registers => .differenced registers
  | .squared registers => .squared registers
  | .products registers => .products registers
  | .summed registers => .summed registers
  | .scaled registers => .scaled registers
  | .done result => .done result

def finiteADCRawReceiverOutput
    {source : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
    {counterBits lastTick : Nat} :
    FiniteADCRawReceiverState source counterBits lastTick → Option (Option FiniteBinaryDrive)
  | .done result => some result
  | _ => none

end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
